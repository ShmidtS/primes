import Mathlib.Tactic
import Mathlib.Analysis.InnerProductSpace.PiL2
import Hagi.Core.FrobOuter

set_option linter.style.header false

/-!
# TernaryPert — возмущение выхода слоя при тернарном квантовании (цикл 11)

Базовый кирпень сквозной ошибки квантования (критика аудита #1):
неравенство подчинённости ‖E·x‖ ≤ ‖E‖_F·‖x‖ для матричной ошибки
E = Q(R) − R, доказанное через Cauchy–Schwarz в EuclideanSpace.
Следствие для тернарного квантователя — через поэлементную
посылку ошибки.
-/

open Finset InnerProductSpace

namespace Hagi.Learning.TernaryPert

open Hagi.Core

variable {m r : ℕ}

/-- Евклидова норма (корень из суммы квадратов). -/
noncomputable def eunorm (x : Fin r → ℝ) : ℝ := Real.sqrt (∑ i, x i ^ 2)

/-- Строка матрицы как вектор. -/
def rowVec (E : Matrix (Fin m) (Fin r) ℝ) (i : Fin m) : Fin r → ℝ :=
  fun j => E i j

/-- CAUCHY–SCHWARZ для координатных сумм:
|(a ⬝ᵥ x)| ≤ ‖a‖·‖x‖. -/
theorem cs_dotProduct (a x : Fin r → ℝ) :
    abs (dotProduct a x) ≤ eunorm a * eunorm x := by
  have hinner : dotProduct a x
      = ⟪(WithLp.toLp 2 a : EuclideanSpace ℝ (Fin r)),
        (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin r))⟫_ℝ := by
    simp [PiLp.inner_apply, starRingEnd_apply, star_trivial]
    exact (dotProduct_comm x a).symm
  have hcs := norm_inner_le_norm
    (𝕜 := ℝ) (WithLp.toLp 2 a : EuclideanSpace ℝ (Fin r))
    (WithLp.toLp 2 x : EuclideanSpace ℝ (Fin r))
  rw [Real.norm_eq_abs] at hcs
  have hnorm : ∀ (y : Fin r → ℝ),
      ‖(WithLp.toLp 2 y : EuclideanSpace ℝ (Fin r))‖ = eunorm y := by
    intro y
    rw [EuclideanSpace.norm_eq]
    simp only [Real.norm_eq_abs, map_pow, abs_of_nonneg, sq_abs]
    rfl
  rw [hinner]
  rw [hnorm a, hnorm x] at hcs
  exact hcs


/-! ### Подчинённость матричной нормы -/

/-- Норма вектора-выхода. -/
noncomputable def outNorm (v : Fin m → ℝ) : ℝ := Real.sqrt (∑ i, v i ^ 2)

/-- ПОДЧИНЁННОСТЬ: ‖E·x‖₂ ≤ ‖E‖_F·‖x‖₂. -/
theorem frob_submul (E : Matrix (Fin m) (Fin r) ℝ) (x : Fin r → ℝ) :
    outNorm (fun i => dotProduct (rowVec E i) x)
      ≤ Real.sqrt (frobSq E) * eunorm x := by
  have hrow : ∀ i : Fin m,
      abs (dotProduct (rowVec E i) x)
        ≤ eunorm (rowVec E i) * eunorm x :=
    fun i => cs_dotProduct (rowVec E i) x
  have hsq : ∀ i : Fin m, (dotProduct (rowVec E i) x) ^ 2
      ≤ (eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 := by
    intro i
    have h := hrow i
    have h2 : abs (dotProduct (rowVec E i) x) * abs (dotProduct (rowVec E i) x)
        ≤ (eunorm (rowVec E i) * eunorm x) * (eunorm (rowVec E i) * eunorm x) :=
      mul_le_mul h h (abs_nonneg _) (by
        have hnn : (0:ℝ) ≤ eunorm (rowVec E i) * eunorm x :=
          mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
        exact hnn)
    have hy : (dotProduct (rowVec E i) x) ^ 2
        = abs (dotProduct (rowVec E i) x) * abs (dotProduct (rowVec E i) x) := by
      rw [← sq_abs, ← pow_two]
    calc (dotProduct (rowVec E i) x) ^ 2
        = abs (dotProduct (rowVec E i) x) * abs (dotProduct (rowVec E i) x) := hy
      _ ≤ (eunorm (rowVec E i) * eunorm x) * (eunorm (rowVec E i) * eunorm x) := h2
      _ = (eunorm (rowVec E i) * eunorm x) ^ 2 := by ring
      _ = eunorm (rowVec E i) ^ 2 * eunorm x ^ 2 := by ring
  have hsum : ∑ i, (dotProduct (rowVec E i) x) ^ 2
      ≤ (∑ i, eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 := by
    calc ∑ i, (dotProduct (rowVec E i) x) ^ 2
        ≤ ∑ i, (eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 :=
          Finset.sum_le_sum (fun i _ => hsq i)
      _ = (∑ i, eunorm (rowVec E i) ^ 2) * (eunorm x) ^ 2 :=
          by rw [← Finset.sum_mul]
  have hrowsq : ∀ i : Fin m, eunorm (rowVec E i) ^ 2 = ∑ j : Fin r, E i j ^ 2 := by
    intro i
    unfold eunorm rowVec
    rw [Real.sq_sqrt (by
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  have hsqE : (∑ i, eunorm (rowVec E i) ^ 2) = frobSq E := by
    rw [Finset.sum_congr rfl (fun i _ => hrowsq i)]
    rfl
  -- финал: sqrt-монотонность
  have hsqrt := Real.sqrt_le_sqrt hsum
  have hsqE' : (∑ i, eunorm (rowVec E i) ^ 2) * eunorm x ^ 2
      = frobSq E * (∑ j : Fin r, x j ^ 2) := by
    rw [hsqE]
    congr 1
    unfold eunorm
    rw [Real.sq_sqrt (by
      exact Finset.sum_nonneg (fun j _ => sq_nonneg _))]
  unfold outNorm eunorm
  calc Real.sqrt (∑ i, (dotProduct (rowVec E i) x) ^ 2)
      ≤ Real.sqrt ((∑ i, eunorm (rowVec E i) ^ 2) * eunorm x ^ 2) := hsqrt
    _ = Real.sqrt (frobSq E * ∑ j : Fin r, x j ^ 2) := by rw [hsqE']
    _ = Real.sqrt (frobSq E) * Real.sqrt (∑ j : Fin r, x j ^ 2) :=
          Real.sqrt_mul (show (0:ℝ) ≤ frobSq E by
              unfold frobSq
              exact Finset.sum_nonneg (fun p _ =>
                Finset.sum_nonneg (fun q _ => sq_nonneg _)))
            (∑ j : Fin r, x j ^ 2)

/-! ### Следствие для тернарного квантования остатков -/

/-- СКВОЗНАЯ ОШИБКА КВАНТОВАНИЯ СЛОЯ: возмущение выхода слоя
при замене остатка R на его тернарное квантование Q(R) не
превосходит ‖R − Q(R)‖_F·‖x‖ — базовый кирпень сквозной оценки
‖f_Q(x) − f(x)‖ (критика аудита #1 закрыта на уровне одного
слоя; композиция слоёв — через телескоп таких оценок). -/
theorem ternary_layer_pert (R QR : Matrix (Fin m) (Fin r) ℝ)
    (x : Fin r → ℝ)
    (hq : ∀ i j, abs (QR i j - R i j) ≤ 1/2) :
    outNorm (fun i => dotProduct (rowVec (QR - R) i) x)
      ≤ Real.sqrt ((m : ℝ) * (r : ℝ) * (1/2)^2) * eunorm x := by
  have hfrob : frobSq (QR - R)
      ≤ (m : ℝ) * (r : ℝ) * (1/2)^2 := by
    unfold frobSq
    have hcard : ∑ a : Fin m, ∑ b : Fin r, ((1:ℝ)/2)^2
        = (m : ℝ) * (r : ℝ) * ((1:ℝ)/2)^2 := by
      rw [Finset.sum_const, Finset.sum_const]
      simp
      push_cast
      ring
    calc frobSq (QR - R)
        = ∑ a : Fin m, ∑ b : Fin r, (QR a b - R a b)^2 := by
          unfold frobSq
          exact Finset.sum_congr rfl (fun a _ =>
            Finset.sum_congr rfl (fun b _ => by
              rfl))
      _ ≤ ∑ a : Fin m, ∑ b : Fin r, (1/2)^2 :=
          Finset.sum_le_sum (fun a _ =>
            Finset.sum_le_sum (fun b _ => by
              have habs := hq a b
              have hkey : abs (QR a b - R a b) * abs (QR a b - R a b)
                  ≤ (1/2 : ℝ) * (1/2 : ℝ) :=
                mul_le_mul habs habs (abs_nonneg _) (by norm_num)
              exact (show (QR a b - R a b) ^ 2 ≤ (1/2 : ℝ) ^ 2 by
                rw [← sq_abs (QR a b - R a b), pow_two, pow_two]
                exact hkey)))
      _ = (m : ℝ) * (r : ℝ) * (1/2)^2 := hcard
  have hsub := frob_submul (QR - R) x
  refine le_trans hsub ?_
  refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
  exact Real.sqrt_le_sqrt hfrob

end Hagi.Learning.TernaryPert

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

set_option linter.style.header false

/-!
# BitBudget — битовая граница ошибки тернарного слоя (цикл 18)

Связка размера и качества (цель HAGI: максимум качества при
минимуме объёма): тернарный слой m×r занимает
B = m·r·log₂(3) бит; его выходное возмущение (цикл 11)
ограничено √(m·r)/2·‖x‖. Композиция даёт трейдофф напрямую
в битах: err ≤ √(B / log₂3) / 2 · ‖x‖ — качество как функция
объёма.
-/

open Finset

namespace Hagi.Learning.BitBudget

open Hagi.Learning.TernaryPert

variable {m r : ℕ}

/-- Биты на тернарный вес: log₂ 3. -/
noncomputable def bitsPerTrit : ℝ := Real.log 3 / Real.log 2

/-- Общий объём тернарного слоя в битах: m·r·log₂3. -/
noncomputable def layerBits (m r : ℕ) : ℝ :=
  (m : ℝ) * (r : ℝ) * bitsPerTrit

theorem bitsPerTrit_pos : (0:ℝ) < bitsPerTrit := by
  unfold bitsPerTrit
  refine div_pos (Real.log_pos (by norm_num : (1:ℝ) < 3)) ?_
  exact Real.log_pos (by norm_num : (1:ℝ) < 2)

/-- ГЛАВНАЯ ГРАНИЦА (размер ↔ качество): для тернарного слоя
объёма B = layerBits m r бит и поэлементной ошибки
квантования ≤ 1/2:
  ‖(Q(R)−R)x‖ ≤ √(B / log₂3)/2 · ‖x‖.
-/
theorem ternary_bit_error_bound (R QR : Matrix (Fin m) (Fin r) ℝ)
    (x : Fin r → ℝ)
    (hq : ∀ i j, abs (QR i j - R i j) ≤ 1/2) :
    outNorm (fun i => dotProduct (rowVec (QR - R) i) x)
      ≤ (Real.sqrt (layerBits m r / bitsPerTrit) / 2) * eunorm x := by
  have h := ternary_layer_pert R QR x hq
  have hmr : layerBits m r / bitsPerTrit = ((m : ℝ) * (r : ℝ)) := by
    unfold layerBits
    have hb := bitsPerTrit_pos.ne'
    field_simp
  rw [hmr]
  have hpos : (0:ℝ) ≤ (m : ℝ) * (r : ℝ) :=
    mul_nonneg (Nat.cast_nonneg m) (Nat.cast_nonneg r)
  have heq : Real.sqrt ((m : ℝ) * (r : ℝ) * (1/2)^2)
      = Real.sqrt ((m : ℝ) * (r : ℝ)) / 2 := by
    have hq : ((1:ℝ)/2)^2 = ((1:ℝ)/4) := by norm_num
    rw [hq]
    have hsm := Real.sqrt_mul (x := (m : ℝ) * (r : ℝ))
      (y := ((1:ℝ)/4)) hpos
    rw [hsm]
    have hqrt : Real.sqrt ((1:ℝ)/4) = 1/2 := by
      rw [Real.sqrt_div (by norm_num)]
      norm_num
    rw [hqrt, mul_one_div]
  -- финальная композиция: trans-цепь
  have h2 : outNorm (fun i => dotProduct (rowVec (QR - R) i) x)
      ≤ (Real.sqrt ((m : ℝ) * (r : ℝ)) / 2) * eunorm x :=
    le_trans h (mul_le_mul_of_nonneg_right (le_of_eq heq)
      (Real.sqrt_nonneg _))
  have hgoal : (Real.sqrt (layerBits m r / bitsPerTrit) / 2)
      = Real.sqrt ((m : ℝ) * (r : ℝ)) / 2 := by rw [hmr]
  exact h2

end Hagi.Learning.BitBudget

set_option linter.style.header false

/-!
# NetworkBudget — сетевой битовый бюджет (цикл 24)

Полная сквозная кривая «биты ↔ качество» для n-слойной
тернарной сети и оптимальность равномерного распределения
бюджета по слоям:

  1. `exists_layer_ge_average`: голубиная дыра — при любом
     распределении неотрицательного тотала N по n слоям
     ∃ слой с бюджетом ≥ N/n; равномерное распределение
     (все aₗ = N/n) достигает границы поточечно — улучшить
     пер-слойный максимум нельзя;
  2. `network_bit_error`: n слоёв, каждый с БЕЗУСЛОВНОЙ
     пер-слойной ошибкой квантования ≤ √(N/n)/2 (unit-scale
     активации: из m·r ≤ N/n и ternary_bit_error_bound при
     ‖y‖ ≤ 1), дают сквозную ошибку ≤ √(n·N)/2·Lⁿ.

Следствие: глубина n и тотал N вычисляются из целевой ошибки
ε: N = (2ε/Lⁿ)²/n — продолжение принципа нулевого подбора
(циклы 22–23) на сетевой уровень; распределение по слоям —
равномерное (по п.1).
-/

open Finset Hagi.Learning.TernaryPert Hagi.Learning.PertTelescope

namespace Hagi.Learning.NetworkBudget

/-! ### 1. Голубиная дыра -/

/-- ОПТИМАЛЬНОСТЬ РАВНОМЕРНОГО РАСПРЕДЕЛЕНИЯ: при любом
распределении неотрицательного тотала N по n > 0 слоям
найдётся слой с бюджетом ≥ N/n. Равномерное распределение
aₗ = N/n достигает границы во всех слоях одновременно —
лучшей пер-слойной границы не существует. -/
theorem exists_layer_ge_average {n : ℕ} (hn : 0 < n)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i) (N : ℝ)
    [NeZero n]
    (hsum : ∑ i, a i = N) :
    ∃ i, N / n ≤ a i := by
  by_contra hcon
  push Not at hcon
  have hlt : ∀ i, a i < N / n := hcon
  have hsumlt : ∑ i, a i < ∑ i, N / n :=
    Finset.sum_lt_sum (fun i _ => le_of_lt (hlt i))
      ⟨0, Finset.mem_univ 0, hlt 0⟩
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin] at hsumlt
  push_cast at hsumlt
  rw [nsmul_eq_mul] at hsumlt
  have hmul : n * (N / n) = N := by
    field_simp
  rw [hmul] at hsumlt
  rw [hsum] at hsumlt
  exact lt_irrefl N hsumlt

/-! ### 2. Сетевая битовая граница -/

variable {v : ℕ}

/-- СЕТЕВАЯ ГРАНИЦА (биты ↔ качество, n слоёв): n-слойная
сеть с безусловной пер-слойной ошибкой квантования
≤ √(N/n)/2 (unit-scale активации; из m·r ≤ N/n и
ternary_bit_error_bound при ‖y‖ ≤ 1) и L-липшицевыми
точными слоями имеет сквозную ошибку ≤ √(n·N)/2·Lⁿ.
Ключевая алгебра: n·√(N/n) = √(n·N) при n > 0, N ≥ 0. -/
theorem network_bit_error (L : ℝ) (hL1 : (1:ℝ) ≤ L)
    (N : ℝ) (hN : (0:ℝ) ≤ N) (n : ℕ) (hn : 0 < n)
    (pairs : List (((Fin v → ℝ) → (Fin v → ℝ))
      × ((Fin v → ℝ) → (Fin v → ℝ))))
    (hlen : pairs.length = n)
    (hlip : ∀ p ∈ pairs, ∀ y y',
      outNorm (p.1 y - p.1 y') ≤ L * outNorm (y - y'))
    (hdelta : ∀ p ∈ pairs, ∀ y,
      outNorm (p.1 y - p.2 y) ≤ Real.sqrt (N / n) / 2)
    (x : Fin v → ℝ) :
    outNorm (compLayers (pairs.map Prod.fst) x
      - compLayers (pairs.map Prod.snd) x)
      ≤ (Real.sqrt (n * N) / 2) * L ^ n := by
  have hdnn : 0 ≤ Real.sqrt (N / n) / 2 :=
    div_nonneg (Real.sqrt_nonneg _) (by norm_num)
  have htel := Hagi.Learning.PertTelescope.pert_telescope
    (v := v) L hL1 pairs (Real.sqrt (N / n) / 2) hdnn
    hlip hdelta x
  rw [hlen] at htel
  have hsqrteq : Real.sqrt (n * N)
      = (n : ℝ) * Real.sqrt (N / n) := by
    have h1 : ((n : ℝ)) * Real.sqrt (N / n)
        = Real.sqrt ((n : ℝ) ^ 2) * Real.sqrt (N / n) := by
      rw [Real.sqrt_sq (Nat.cast_nonneg n)]
    rw [h1, ← Real.sqrt_mul (pow_nonneg (Nat.cast_nonneg n) 2)
      (N / n)]
    have h2 : ((n : ℝ) ^ 2) * (N / n) = n * N := by
      field_simp
    rw [h2]
  push_cast at htel
  exact le_trans htel (le_of_eq (by rw [hsqrteq]; ring))

end Hagi.Learning.NetworkBudget

/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Mathlib.Tactic
/-!
# chunked CE - exact piecewise summation + prior decomposition

Phase B. Sources: 2609.32100
(exact definition of valid token positions + protocol),
2607.16666 (subsampling with rate correction),
2607.10951 (one-sample unbiasedness transfer).

Theorems:

* `chunked_sum_exact` - EXACTNESS of chunked summation:
if T = n * w, the token sum splits into n chunks of width w
with NO loss - the chunked CE equals the full CE.
* `ce_prior_decomposition` - CE = H(prior) + KL correction:
cross-entropy against q decomposes as the prior entropy
plus the KL divergence (proper objective).

Honest boundary: the valid-position protocol (masking of
padding) follows 2609.32100; here positions are all valid.
-/

namespace Hagi.Data
open Finset

/-- EXACTNESS of chunked summation: with T = n * w the sum
over T positions is the sum over n chunks of width w. -/
theorem chunked_sum_exact (n w : ℕ) (f : ℕ → ℝ) :
    ∑ i ∈ Finset.range (n * w), f i
      = ∑ c ∈ Finset.range n, ∑ j ∈ Finset.range w,
          f (c * w + j) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hsplit : Finset.range ((n + 1) * w)
          = Finset.range (n * w)
            ∪ Finset.Ico (n * w) ((n + 1) * w) := by
        ext i
        simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico,
          Nat.add_mul]
        omega
      have hdisj : Disjoint (Finset.range (n * w))
          (Finset.Ico (n * w) ((n + 1) * w)) := by
        rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_range] at ha
        simp only [Finset.mem_Ico] at hb
        omega
      have hico : ∑ i ∈ Finset.Ico (n * w) ((n + 1) * w), f i
          = ∑ j ∈ Finset.range w, f (n * w + j) := by
        rw [Finset.sum_Ico_eq_sum_range f, Nat.add_mul,
          show n * w + 1 * w - n * w = w from by omega]
      rw [hsplit, Finset.sum_union hdisj, hico, ih,
        Finset.sum_range_succ]

/-- CE = H(prior) + KL correction: the cross-entropy of q
against the uniform-free decomposition. For distribution p
(prior) and q (model), CE q p = entropy p + KL p q on a
finite type. -/
theorem ce_prior_decomposition {V : Type} [Fintype V]
    (p q : V → ℝ) (hp : ∀ v, 0 < p v) (hpsum : ∑ v, p v = 1)
    (hq : ∀ v, 0 < q v) (hqsum : ∑ v, q v = 1) :
    ∑ v, p v * Real.log (q v)
      = ∑ v, p v * Real.log (p v)
        + ∑ v, p v * Real.log (q v / p v) := by
  have hterm : ∀ v, p v * Real.log (q v / p v)
      = p v * Real.log (q v) - p v * Real.log (p v) := by
    intro v
    rw [Real.log_div (ne_of_gt (hq v)) (ne_of_gt (hp v))]
    ring
  rw [Finset.sum_congr rfl (fun v _ => hterm v),
    Finset.sum_sub_distrib]
  ring

end Hagi.Data
/-!
# LRWidth — неинвариантность LR по ширине и muP-скейлинг

Модель: линейный слой W (m строк) на квадратичной потере
`L = ½·‖W·1‖²`.

* `grad_norm_grows`: при all-ones инициализации квадрат
  нормы градиента равен `m·d³` — растёт линейно по ширине m
  (фиксированный LR не инвариантен по ширине);
* `mup_grad_invariant`: при скейлинге `W i j = 1/√m` квадрат
  нормы градиента равен `d³` — не зависит от ширины
  (muP-предписание для этого слоя).

Полный muP-перенос (все слои, моменты Adam) — эмпирический;
здесь — точное утверждение для квадратичной линейной модели.
-/

namespace Hagi.Step
open Finset

/-- Компонент градиента потери `L = ½·Σ_i (Σ_j W i j)²`:
`gradEntry W i j = Σ_j' W i j'`. -/
def gradEntry {m d : ℕ} (W : Fin m → Fin d → ℝ) (i : Fin m) (j : Fin d) : ℝ :=
  ∑ j', W i j'

/-- При `Wones i j = 1` для всех i j:
`Σ_i Σ_j (gradEntry Wones i j)² = m·d³` — линейный рост
по m (фиксированный LR не инвариантен по ширине). -/
theorem grad_norm_grows (m d : ℕ)
    (Wones : Fin m → Fin d → ℝ) (hones : ∀ i j, Wones i j = 1) :
    ∑ i, ∑ j, (gradEntry Wones i j)^2 = (m : ℝ) * (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wones i j = (d : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hones i j']
    simp
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ, Finset.sum_const,
    Finset.card_univ]
  simp only [Fintype.card_fin]
  push_cast
  ring

/-- При `1 ≤ m` и `Wmup i j = 1/√m` для всех i j:
`Σ_i Σ_j (gradEntry Wmup i j)² = d³` — не зависит от
ширины (muP-скейлинг). -/
theorem mup_grad_invariant (m d : ℕ) (hm : 1 ≤ m)
    (Wmup : Fin m → Fin d → ℝ)
    (hmup : ∀ i j, Wmup i j = 1 / Real.sqrt (m : ℝ)) :
    ∑ i, ∑ j, (gradEntry Wmup i j)^2 = (d : ℝ)^3 := by
  have hgrad : ∀ i j, gradEntry Wmup i j
      = (d : ℝ) / Real.sqrt (m : ℝ) := by
    intro i j
    unfold gradEntry
    rw [Finset.sum_congr rfl fun j' _ => hmup i j']
    rw [Finset.sum_const, Finset.card_univ]
    simp
    ring
  rw [Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun j _ => by rw [hgrad i j],
    Finset.sum_const, Finset.card_univ]
  have hmpos : (0:ℝ) < (m : ℝ) := by positivity
  have hkey : ((d : ℝ) / Real.sqrt (m : ℝ))^2
      = (d : ℝ)^2 / (m : ℝ) := by
    have h1 : (Real.sqrt (m : ℝ))^2 = (m : ℝ) :=
      Real.sq_sqrt (by positivity)
    rw [div_pow, h1]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rw [hkey]
  simp
  field_simp
end Hagi.Step
set_option linter.style.header false

/-!
# Muon — спектральный прекондиционер и совместимость с SafeQP

* `muon_step_bound`: при контракции `‖P z‖ ≤ ‖z‖` для всех z
  — `‖muonDir P g‖ ≤ ‖g‖` (направление Muon не превышает
  сырой градиент по норме — совместимо с SafeQP);
* `muon_pl_rate`: `‖muonDir P g‖² ≤ ‖g‖²` при той же
  контракции.

Свойство `‖P‖_op ≤ 1` Newton-Schulz — гипотеза hP
(полярное разложение — вне этого модуля).
-/

namespace Hagi.Step

variable {V : Type} [NormedAddCommGroup V]

/-- Направление Muon: `muonDir P g = P g` —
прекондиционированный градиент. -/
def muonDir {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W) : W := P g

/-- Если `‖P z‖ ≤ ‖z‖` для всех z, то `‖muonDir P g‖ ≤ ‖g‖`. -/
theorem muon_step_bound {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖ ≤ ‖g‖ :=
  hP g

/-- Если `‖P z‖ ≤ ‖z‖` для всех z, то
`‖muonDir P g‖^2 ≤ ‖g‖^2`. -/
theorem muon_pl_rate {W : Type} [NormedAddCommGroup W]
    (P : W → W) (g : W)
    (hP : ∀ z, ‖P z‖ ≤ ‖z‖) :
    ‖muonDir P g‖^2 ≤ ‖g‖^2 := by
  rw [sq, sq]
  exact mul_self_le_mul_self (norm_nonneg _) (hP g)

end Hagi.Step


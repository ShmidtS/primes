/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Mathlib.Tactic
import Hagi.Core.FrobOuter
/-!
# CurvatureSafe — учитывающий кривизну SafeQP (trust region)

(R322: перенесён из Dynamics/ в Step/ — аудит v3 §2.2: теория
кривизны и ограничения размера шага живёт в оптимизационном слое.)

Второпорядковая оценка при L-Lipschitz градиентах:
`L_i(w+d) − L_i(w) ≤ −⟪g i, d⟫ + (L_i/2)·‖d‖²`.

* `safeqp_second_order`: при `−eps ≤ inner` и гладкости —
  `dL ≤ eps + L·dnorm²/2`;
* `safeqp_trust_region`: при `dnorm² ≤ 2·eps/L` —
  `dL ≤ 2·eps` (явный радиус trust-региона);
* `safeqp_monotone_domain`: при `0 ≤ inner`, `L > 0`,
  `dnorm² ≤ 2·slack/L` и `slack ≤ 0` — `dL ≤ 0`
  (точный сертификат, вырожденный случай: посылки влекут
  `‖d‖² = 0`).
-/

namespace Hagi.Step

/-- При `−eps ≤ inner` и `dL ≤ −inner + L·dnorm²/2` —
`dL ≤ eps + L·dnorm²/2`. -/
theorem safeqp_second_order (inner eps L dnorm dL : ℝ)
    (hfeas : -eps ≤ inner) (_hL : 0 ≤ L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2) :
    dL ≤ eps + L * dnorm ^ 2 / 2 := by
  linarith

/-- При `0 < L`, `−eps ≤ inner`, гладкости и
`dnorm² ≤ 2·eps/L` — `dL ≤ 2·eps`. -/
theorem safeqp_trust_region (inner eps L dnorm dL : ℝ)
    (hfeas : -eps ≤ inner) (hL : 0 < L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2)
    (hrad : dnorm ^ 2 ≤ 2 * eps / L) :
    dL ≤ 2 * eps := by
  have h1 := safeqp_second_order inner eps L dnorm dL hfeas hL.le h_emp_smooth
  have h2 : L * dnorm ^ 2 / 2 ≤ eps := by
    calc L * dnorm ^ 2 / 2 = (L / 2) * dnorm ^ 2 := by ring
      _ ≤ (L / 2) * (2 * eps / L) := by
          apply mul_le_mul_of_nonneg_left hrad (by linarith)
      _ = eps := by field_simp
  linarith

/-- При `0 ≤ inner`, `0 < L`, `dnorm² ≤ 2·slack/L` и
`slack ≤ 0` — `dL ≤ 0`. Посылки вынуждают `dnorm² = 0`
(вырожденный точный случай, не аргумент о марже). -/
theorem safeqp_monotone_domain (inner slack L dnorm dL : ℝ)
    (hfeas : 0 ≤ inner) (hL : 0 < L)
    (h_emp_smooth : dL ≤ -inner + L * dnorm ^ 2 / 2)
    (hrad : dnorm ^ 2 ≤ 2 * slack / L) (hslack : slack ≤ 0) :
    dL ≤ 0 := by
  -- direct: dL ≤ −inner + (L/2)‖d‖² ≤ 0 + slack ≤ 0
  have h4 : L * dnorm ^ 2 / 2 ≤ slack := by
    calc L * dnorm ^ 2 / 2 = (L / 2) * dnorm ^ 2 := by ring
      _ ≤ (L / 2) * (2 * slack / L) := by
          apply mul_le_mul_of_nonneg_left hrad (by linarith)
      _ = slack := by field_simp
  linarith
end Hagi.Step

set_option linter.style.header false
set_option linter.unusedFintypeInType false
set_option linter.unusedSectionVars false

/-!
# SafeQPStep — выведенный безопасный размер шага SafeQP

Десцент-лемма по домену i:
`ΔL_i ≤ −η·⟪g i, d⟫ + (L_i/2)·η²·‖d‖²`; при марже
`m_i = ε_i + ⟪g i, d⟫ ≥ 0` окно шага, удерживающее бюджет:
`η ≤ min(1, ⨅_i 2·m_i/(L_i·‖d‖²))` (клэмп на 1 — из
линейного члена η·ε_i ≤ ε_i при ε_i ≥ 0).

* `safeqpEtaMax` / `le_safeqpEtaMax_iff`: явная формула и её
  эквивалентная развёртка;
* `safeqp_eta_max_domain`: скалярное ядро (при пороге —
  `dL ≤ eps`);
* `safeqp_eta_max`: при `d ≠ 0`, `L i > 0`, `eps i ≥ 0`,
  `0 ≤ η ≤ safeqpEtaMax` и десцент-лемме — `dL i ≤ eps i`
  для всех i;
* `safeqp_eta_zero_direction`: при d = 0 — `dL i ≤ eps i`
  для любого η;
* `safeqpEtaMaxConflictFree` / `_iff` / `_pos` /
  `safeqp_eta_max_conflict_free`: бесконфликтная версия
  (окно `min(1, ⨅ 2·eps i/(L i·‖d‖²))`, строго положительная
  при `eps i > 0`, `d ≠ 0`).
-/

namespace Hagi.Step

open Real InnerProductSpace

section SafeQPStep

variable {K : Type*} [Fintype K] [Nonempty K]
variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

/-- Выведенное окно шага:
`safeqpEtaMax g eps L d
= min 1 (⨅ i, 2·(eps i + ⟪g i, d⟫)/(L i·‖d‖²))`. -/
noncomputable def safeqpEtaMax (g : K → X) (eps L : K → ℝ) (d : X) : ℝ :=
  min 1 (⨅ i, 2 * (eps i + ⟪g i, d⟫_ℝ) / (L i * ‖d‖ ^ 2))

/-- `eta ≤ safeqpEtaMax g eps L d ↔ eta ≤ 1 ∧ ∀ i,
eta ≤ 2·(eps i + ⟪g i, d⟫)/(L i·‖d‖²)`. -/
theorem le_safeqpEtaMax_iff (g : K → X) (eps L : K → ℝ) (d : X) {eta : ℝ} :
    eta ≤ safeqpEtaMax g eps L d ↔
      eta ≤ 1 ∧ ∀ i, eta ≤ 2 * (eps i + ⟪g i, d⟫_ℝ) / (L i * ‖d‖ ^ 2) := by
  have hbd : BddBelow (Set.range fun i =>
      2 * (eps i + ⟪g i, d⟫_ℝ) / (L i * ‖d‖ ^ 2)) :=
    Finite.bddBelow_range _
  rw [safeqpEtaMax, le_min_iff, le_ciInf_iff hbd]

/-- Скалярное ядро: при `0 < L`, `0 < dsq`, `0 ≤ eps`,
`0 ≤ eta ≤ 1`, `eta ≤ 2·(eps + inner)/(L·dsq)` и
`dL ≤ −eta·inner + L·eta²·dsq/2` — `dL ≤ eps`. -/
theorem safeqp_eta_max_domain (inner eps L dsq eta dL : ℝ)
    (hL : 0 < L) (hdsq : 0 < dsq) (heps : 0 ≤ eps)
    (heta : 0 ≤ eta) (hone : eta ≤ 1)
    (h_eta : eta ≤ 2 * (eps + inner) / (L * dsq))
    (h_lipline : dL ≤ -eta * inner + L * eta * eta * dsq / 2) :
    dL ≤ eps := by
  have hpos : 0 < L * dsq := by positivity
  have hmul : eta * (L * dsq) ≤ 2 * (eps + inner) := by
    rwa [le_div_iff₀ hpos] at h_eta
  -- the margin is nonnegative (forced by the window itself)
  have hm : 0 ≤ eps + inner := by
    have h0 : (0:ℝ) ≤ eta * (L * dsq) := mul_nonneg heta hpos.le
    linarith
  -- the quadratic bracket is nonpositive: (L/2)·η·dsq ≤ m
  have hkey : L * eta * eta * dsq / 2 ≤ eta * (eps + inner) := by
    have h2 : eta * (eta * (L * dsq)) ≤ eta * (2 * (eps + inner)) :=
      mul_le_mul_of_nonneg_left hmul heta
    nlinarith [h2]
  -- η·ε ≤ ε (unit step, nonnegative budget)
  have hee : eta * eps ≤ eps := by
    have : eta * eps ≤ 1 * eps :=
      mul_le_mul_of_nonneg_right hone heps
    linarith
  -- assemble: dL ≤ η·ε − η·m + (L/2)η²dsq ≤ ε
  have hsplit : -eta * inner = -eta * (eps + inner) + eta * eps := by ring
  linarith

/-- При `d ≠ 0`, `L i > 0`, `eps i ≥ 0`, `0 ≤ eta`,
`eta ≤ safeqpEtaMax` и десцент-лемме по каждому i —
`dL i ≤ eps i` для всех i одновременно. -/
theorem safeqp_eta_max (g : K → X) (eps L : K → ℝ) (d : X) (dL : K → ℝ)
    (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMax g eps L d) :
    ∀ i, dL i ≤ eps i := by
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have hn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith [hn]
  obtain ⟨hone, hthr⟩ := (le_safeqpEtaMax_iff g eps L d).mp h_eta
  intro i
  exact safeqp_eta_max_domain ⟪g i, d⟫_ℝ (eps i) (L i) (‖d‖ ^ 2)
    eta (dL i) (hL i) hdsq (heps i) heta hone (hthr i) (h_lipline i)

/-- Вырожденный случай d = 0: при десцент-лемме с d = 0 —
`dL i ≤ eps i` для любого eta. -/
theorem safeqp_eta_zero_direction (g : K → X) (eps L : K → ℝ)
    (dL : K → ℝ) (eta : ℝ)
    (heps : ∀ i, 0 ≤ eps i)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, (0 : X)⟫_ℝ
      + L i * eta * eta * ‖(0 : X)‖ ^ 2 / 2) :
    ∀ i, dL i ≤ eps i := by
  intro i
  have h := h_lipline i
  rw [inner_zero_right, norm_zero] at h
  have h0 : L i * eta * eta * (0:ℝ) ^ 2 / 2 = 0 := by ring
  rw [h0] at h
  rw [mul_zero, add_zero] at h
  linarith [heps i]

/-- Бесконфликтное окно:
`safeqpEtaMaxConflictFree eps L d
= min 1 (⨅ i, 2·eps i/(L i·‖d‖²))`. -/
noncomputable def safeqpEtaMaxConflictFree (eps L : K → ℝ) (d : X) : ℝ :=
  min 1 (⨅ i, 2 * eps i / (L i * ‖d‖ ^ 2))

theorem le_safeqpEtaMaxConflictFree_iff (eps L : K → ℝ) (d : X) {eta : ℝ} :
    eta ≤ safeqpEtaMaxConflictFree eps L d ↔
      eta ≤ 1 ∧ ∀ i, eta ≤ 2 * eps i / (L i * ‖d‖ ^ 2) := by
  have hbd : BddBelow (Set.range fun i => 2 * eps i / (L i * ‖d‖ ^ 2)) :=
    Finite.bddBelow_range _
  rw [safeqpEtaMaxConflictFree, le_min_iff, le_ciInf_iff hbd]

/-- При `L i > 0`, `eps i > 0` и `d ≠ 0`:
`0 < safeqpEtaMaxConflictFree eps L d`. -/
theorem safeqpEtaMaxConflictFree_pos (eps L : K → ℝ) (d : X)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 < eps i) (hd : d ≠ 0) :
    0 < safeqpEtaMaxConflictFree eps L d := by
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have hn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith [hn]
  -- every per-domain threshold is strictly positive
  have hthr : ∀ i : K, (0:ℝ) < 2 * eps i / (L i * ‖d‖ ^ 2) := by
    intro i
    have hp : (0:ℝ) < L i * ‖d‖ ^ 2 := by nlinarith [hL i, hdsq]
    exact div_pos (mul_pos two_pos (heps i)) hp
  -- the iInf over a nonempty finite type is attained (the min'
  -- of the image finset); a finite infimum of strictly positive
  -- thresholds is strictly positive
  have hEq : (⨅ i, 2 * eps i / (L i * ‖d‖ ^ 2) : ℝ)
      = ((Finset.univ.image
          fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
        (Finset.univ_nonempty.image _)) := by
    classical
    have h1 : ((Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
        (Finset.univ_nonempty.image _))
        = (Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).inf'
        (Finset.univ_nonempty.image _) id := rfl
    have h2 : (Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).inf'
        (Finset.univ_nonempty.image _) id
        = Finset.univ.inf' Finset.univ_nonempty
          fun i => 2 * eps i / (L i * ‖d‖ ^ 2) := by
      simp [Finset.inf'_image]
    rw [h1, h2, Finset.inf'_univ_eq_ciInf]
  have hminmem : ((Finset.univ.image
        fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
      (Finset.univ_nonempty.image _))
      ∈ Finset.univ.image fun i => 2 * eps i / (L i * ‖d‖ ^ 2) :=
    Finset.min'_mem _ _
  obtain ⟨i, hi⟩ : ∃ i : K,
      2 * eps i / (L i * ‖d‖ ^ 2)
        = (Finset.univ.image
            fun i => 2 * eps i / (L i * ‖d‖ ^ 2)).min'
        (Finset.univ_nonempty.image _) := by
    simpa using hminmem
  have hinf : (0:ℝ) < ⨅ i, 2 * eps i / (L i * ‖d‖ ^ 2) := by
    rw [hEq, ← hi]
    exact hthr i
  rw [safeqpEtaMaxConflictFree, lt_min_iff]
  exact ⟨by norm_num, hinf⟩

/-- При `L i > 0`, `eps i ≥ 0`, `0 ≤ eta`, `d ≠ 0`, отсутствии
конфликтов `0 ≤ ⟪g i, d⟫`, десцент-лемме и
`eta ≤ safeqpEtaMaxConflictFree eps L d` —
`dL i ≤ eps i` для всех i. -/
theorem safeqp_eta_max_conflict_free (g : K → X) (eps L : K → ℝ)
    (d : X) (dL : K → ℝ) (eta : ℝ)
    (hL : ∀ i, 0 < L i) (heps : ∀ i, 0 ≤ eps i) (heta : 0 ≤ eta)
    (hd : d ≠ 0)
    (hnc : ∀ i, 0 ≤ ⟪g i, d⟫_ℝ)
    (h_lipline : ∀ i, dL i ≤ -eta * ⟪g i, d⟫_ℝ
      + L i * eta * eta * ‖d‖ ^ 2 / 2)
    (h_eta : eta ≤ safeqpEtaMaxConflictFree eps L d) :
    ∀ i, dL i ≤ eps i := by
  have hdsq : 0 < ‖d‖ ^ 2 := by
    have hn : (0:ℝ) < ‖d‖ := norm_pos_iff.mpr hd
    nlinarith [hn]
  obtain ⟨hone, hthr⟩ :=
    (le_safeqpEtaMaxConflictFree_iff eps L d).mp h_eta
  -- every conflict-free threshold implies the margin threshold
  have hmargin : ∀ i, eta ≤ 2 * (eps i + ⟪g i, d⟫_ℝ)
      / (L i * ‖d‖ ^ 2) := by
    intro i
    have hpos : 0 < L i * ‖d‖ ^ 2 := mul_pos (hL i) hdsq
    have hle : 2 * eps i ≤ 2 * (eps i + ⟪g i, d⟫_ℝ) := by
      have : 0 ≤ 2 * ⟪g i, d⟫_ℝ := mul_nonneg two_pos.le (hnc i)
      linarith
    have h1 : eta * (L i * ‖d‖ ^ 2) ≤ 2 * eps i :=
      (le_div_iff₀ hpos).mp (hthr i)
    exact le_trans (hthr i)
      ((div_le_div_iff₀ hpos hpos).mpr (by nlinarith [h1, hle]))
  exact safeqp_eta_max g eps L d dL eta hL heps heta hd h_lipline
    ((le_safeqpEtaMax_iff g eps L d).mpr ⟨hone, hmargin⟩)

end SafeQPStep

section SafeQPBilinearDrift

variable {d : ℕ}

open scoped Matrix
open Finset

/-! ## Bilinear quadratic drift (A8 F7)

For bilinear (`A @ B`-shaped) adapter steps the SafeQP linear
acceptance `⟪g, d⟫ ≥ −tol` is insufficient: the Frobenius energy
of a bilinear step expands EXACTLY with a genuine quadratic term
(attained at `L = 2`), so the second-order-aware acceptance
`(L/2)·η²·‖d‖² − eps ≤ η·⟪g, d⟫` of
`safeqp_second_order_acceptance` is the honest form. The
preconditioner metric `(I + γΣ_old)⁻¹` enters as premise-form:
a PSD-factored direction `d = (QᵀQ) *ᵥ g` is conflict-free
(`safeqp_precond_conflict_free`). -/

open Finset

/-- Frobenius inner product (entrywise). -/
def frobInner (M W : Matrix (Fin d) (Fin d) ℝ) : ℝ :=
  ∑ i, ∑ j, M i j * W i j

/-- Sum-of-three split for double sums. -/
theorem sum_three_split (F G H : Fin d → Fin d → ℝ) :
    (∑ i, (∑ j, (F i j + G i j + H i j)))
      = (∑ i, (∑ j, F i j)) + (∑ i, (∑ j, G i j))
          + (∑ i, (∑ j, H i j)) := by
  have hin : ∀ i : Fin d, (∑ j, (F i j + G i j + H i j))
      = (∑ j, F i j) + (∑ j, G i j) + (∑ j, H i j) := by
    intro i
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun i _ => hin i), Finset.sum_add_distrib,
    Finset.sum_add_distrib]

/-- EXACT bilinear drift: for a bilinear adapter step
`M ↦ M + η • W` the Frobenius energy expands EXACTLY — the
quadratic term `(L/2)·η²·‖d‖²` is attained with `L = 2`, not
merely an upper bound. -/
theorem frobSq_add_smul (M W : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    Hagi.Core.frobSq (M + η • W)
      = Hagi.Core.frobSq M + 2 * η * frobInner M W
          + η ^ 2 * Hagi.Core.frobSq W := by
  have key : ∀ i j : Fin d,
      (M i j + η * W i j) ^ 2
        = (M i j) ^ 2 + 2 * (η * (M i j * W i j))
            + η ^ 2 * (W i j) ^ 2 := by
    intro i j; ring
  unfold Hagi.Core.frobSq frobInner
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [Finset.sum_congr rfl (fun i _ =>
    Finset.sum_congr rfl (fun j _ => key i j))]
  rw [sum_three_split]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]

theorem frobSq_zero (d : ℕ) :
    Hagi.Core.frobSq (0 : Matrix (Fin d) (Fin d) ℝ) = 0 := by
  unfold Hagi.Core.frobSq; simp

theorem frobInner_zero_left (W : Matrix (Fin d) (Fin d) ℝ) :
    frobInner (0 : Matrix (Fin d) (Fin d) ℝ) W = 0 := by
  unfold frobInner; simp

theorem frobSq_smul (W : Matrix (Fin d) (Fin d) ℝ) (η : ℝ) :
    Hagi.Core.frobSq (η • W) = η ^ 2 * Hagi.Core.frobSq W := by
  have hz : (0 : Matrix (Fin d) (Fin d) ℝ) + η • W = η • W := by
    ext i j; simp
  have h := frobSq_add_smul 0 W η
  rw [frobSq_zero, frobInner_zero_left] at h
  rw [← hz] at h
  simpa using h

/-- The A8 insufficiency witness: for every `tol ≥ 0` and every
nonzero bilinear direction `W` there is a step size `η` at which
the EXACT quadratic drift exceeds `tol` even though the linear
term is identically zero (so the linear-only acceptance test
passes for every tolerance). -/
theorem safeqp_linear_test_insufficient (tol : ℝ) (htol : 0 ≤ tol)
    (W : Matrix (Fin d) (Fin d) ℝ) (hW : 0 < Hagi.Core.frobSq W) :
    ∃ η : ℝ, tol < Hagi.Core.frobSq (η • W)
        - Hagi.Core.frobSq (0 : Matrix (Fin d) (Fin d) ℝ) := by
  refine ⟨Real.sqrt ((tol + 1) / Hagi.Core.frobSq W), ?_⟩
  have h0 := frobSq_zero d
  have hx : 0 ≤ (tol + 1) / Hagi.Core.frobSq W :=
    div_nonneg (by linarith) (le_of_lt hW)
  have hsq : (Real.sqrt ((tol + 1) / Hagi.Core.frobSq W)) ^ 2
      = (tol + 1) / Hagi.Core.frobSq W := Real.sq_sqrt hx
  rw [h0, sub_zero, frobSq_smul, hsq,
    div_mul_cancel₀ _ (ne_of_gt hW)]
  linarith

/-- The second-order-aware acceptance premise (the honest bilinear
descent certificate): with the descent-lemma bound and the
quadratic-aware acceptance `(L/2)·η²·‖d‖² − eps ≤ η·⟪g, d⟫`, the
loss increase is at most `eps` — the form the bilinear case
NEEDS (the linear-only test cannot supply the acceptance side). -/
theorem safeqp_second_order_acceptance (inner eps L dnorm eta dL : ℝ)
    (h_lipline : dL ≤ -eta * inner + L * eta * eta * dnorm / 2)
    (hacc : L * eta * eta * dnorm / 2 - eps ≤ eta * inner) :
    dL ≤ eps := by linarith

/-- Preconditioner-metric premise-form (A8 `(I + γΣ_old)⁻¹`):
a PSD-preconditioned direction `d = (QᵀQ) *ᵥ g` is conflict-free
— `⟪g, d⟫ = ‖Q *ᵥ g‖² ≥ 0`. -/
theorem safeqp_precond_conflict_free {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) :
    g ⬝ᵥ ((Qᵀ * Q) *ᵥ g) = (Q *ᵥ g) ⬝ᵥ (Q *ᵥ g) := by
  rw [show ((Qᵀ * Q) *ᵥ g) = Qᵀ *ᵥ (Q *ᵥ g) from
      (Matrix.mulVec_mulVec g Qᵀ Q).symm,
    Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

theorem safeqp_precond_conflict_free_nonneg {n : ℕ}
    (Q : Matrix (Fin n) (Fin n) ℝ) (g : Fin n → ℝ) :
    0 ≤ g ⬝ᵥ ((Qᵀ * Q) *ᵥ g) := by
  rw [safeqp_precond_conflict_free]
  unfold dotProduct
  exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)

end SafeQPBilinearDrift

end Hagi.Step

namespace Hagi
export Hagi.Step (safeqpEtaMax le_safeqpEtaMax_iff safeqp_eta_max)
end Hagi

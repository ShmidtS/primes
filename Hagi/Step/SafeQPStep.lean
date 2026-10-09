/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Dynamics.CurvatureSafe

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

namespace Hagi

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

end Hagi

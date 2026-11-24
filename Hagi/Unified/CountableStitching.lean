/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Unified.StitchingEProcess
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Countable stitching of e-processes

The countable-family extension of the finite stitching gate
(`Hagi.Unified.StitchingEProcess`): given a COUNTABLE family
of nonnegative anytime e-processes `E k` on ℕ with summable
nonnegative prior weights, the tsum-mixture master
`M t = ∑' k, w k * E k t` inherits the Ville time-uniform
false-alarm control.

Reduction route: the finite carrier mixes ALL
components at ALL times — there is no activation schedule — so the
honest reduction is the MONOTONE FINITE-PREFIX route: the strict
alarm set at level `c` sits inside the increasing union of the
finite-prefix alarm sets, each bounded by the existing finite
theorem `stitching_eprocess_anytime`; continuity from below
(`Monotone.measure_iUnion`) converts the union into the level
bound `μ.real ≤ c⁻¹`; the Ville threshold is then reached by an
archimedean squeeze. The finite engine is reused verbatim; NO new
concentration mathematics.

* `stitchedMasterCountable` — the tsum-mixture master process.
* `stitching_countable_initial_mass` — `μ[M 0] = ∑' k, w k * μ[E k 0]`
  (the countable analogue of `stitching_master_initial_mass`; the
  tsum/integral interchange is `integral_tsum` +
  `ofReal_integral_norm_eq_lintegral_enorm`).
* `stitching_countable_ville` — MAIN: with `∑' k, w k ≤ 1` and
  `0 < δ`: `μ.real {∃ t ≤ n, δ⁻¹ ≤ M t} ≤ δ` for every horizon `n`
  at once, matching the finite statement's shape exactly.
* `stitching_countable_geometric_weights` — the geometric schedule
  `w k = 2^{-(k+1)}` sums to exactly 1 (numeric anchor; a concrete
  countable stitch instance with summability PROVEN).

Honesty boundaries (documented deferrals):

* `Summable w` is a LOAD-BEARING premise of the main theorem, not
  decoration: for a non-summable nonnegative `w` the ℝ-tsum is junk
  (`∑' w = 0 ≤ 1` holds vacuously) while the finite prefixes are
  unbounded — e.g. `w k = (3/2)^k` with `E k ≡ 2^{-k}` satisfies
  every other premise and violates the conclusion. The pointwise
  mixture summability premise `hsum` carries the a.e./pointwise
  side of the countable bookkeeping.
* The countable SUPERMARTINGALE closure (conditional expectation of
  the tsum) is NOT claimed anywhere in this file — it is not needed
  for the Ville transfer and is not proved; the master is certified
  only through its finite prefixes.
* As in the finite file, each `E k` is a hypothesis (premise form);
  this file proves the stitching transfer, not the construction of
  the per-expert e-processes.
-/

open Finset MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

namespace Hagi.Unified

variable {Ω : Type*} {m0 : MeasurableSpace Ω} {μ : Measure Ω}
  {𝒢 : Filtration ℕ m0}

/-- The countable stitched master: `M t = ∑' k, w k * E k t`. -/
noncomputable def stitchedMasterCountable (w : ℕ → ℝ) (E : ℕ → ℕ → Ω → ℝ) : ℕ → Ω → ℝ :=
  fun t ω => ∑' k, w k * E k t ω

variable (w : ℕ → ℝ) (E : ℕ → ℕ → Ω → ℝ)

/-- Partial-sum value of the finite master on `Fin (K+1)`. -/
private lemma finMaster_eq (K t : ℕ) (ω : Ω) :
    stitchedMaster (fun i : Fin (K + 1) => w i) (fun i : Fin (K + 1) => E i) t ω
      = ∑ k ∈ Finset.range (K + 1), w k * E k t ω := by
  simp only [stitchedMaster, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  exact Fin.sum_univ_eq_sum_range (fun k => w k * E k t ω) (K + 1)

/-- Partial sums are monotone in the prefix length. -/
private lemma rangeSum_mono (hw : ∀ k, 0 ≤ w k) (hEnn : ∀ k t ω, 0 ≤ E k t ω)
    {K K' : ℕ} (hKK : K ≤ K') (t : ℕ) (ω : Ω) :
    ∑ k ∈ Finset.range (K + 1), w k * E k t ω
      ≤ ∑ k ∈ Finset.range (K' + 1), w k * E k t ω := by
  have hss : Finset.range (K + 1) ⊆ Finset.range (K' + 1) := by
    intro x hx
    have hx' := Finset.mem_range.1 hx
    exact Finset.mem_range.2 (by omega)
  exact Finset.sum_le_sum_of_subset_of_nonneg hss
    (fun k _ _ => mul_nonneg (hw k) (hEnn k t ω))

/-- If a series has tsum above `c`, some partial sum is above `c`. -/
private lemma exists_partial_gt {f : ℕ → ℝ} (hs : Summable f) {c : ℝ}
    (hc : c < ∑' k, f k) :
    ∃ K : ℕ, c ≤ ∑ k ∈ Finset.range K, f k := by
  by_contra hcon
  push Not at hcon
  have htend : Tendsto (fun K => ∑ k ∈ Finset.range K, f k) atTop
      (𝓝 (∑' k, f k)) := hs.hasSum.tendsto_sum_nat
  have hmem : Set.Ioo (c + (∑' k, f k - c) / 2) (∑' k, f k + 1)
      ∈ 𝓝 (∑' k, f k) :=
    isOpen_Ioo.mem_nhds ⟨by linarith, by linarith⟩
  obtain ⟨N, hN⟩ := eventually_atTop.1 (htend.eventually hmem)
  have hKS := Set.mem_Ioo.1 (hN N (le_refl N))
  linarith [hcon N, hKS.1, hKS.2]

/-- Finite-prefix weights sum below the tsum. -/
private lemma finsum_w_le (hw : ∀ k, 0 ≤ w k) (hwsumm : Summable w)
    (hwsum : ∑' k, w k ≤ 1) (K : ℕ) :
    ∑ i : Fin (K + 1), w i ≤ 1 := by
  calc ∑ i : Fin (K + 1), w i = ∑ k ∈ Finset.range (K + 1), w k :=
        Fin.sum_univ_eq_sum_range _ _
    _ ≤ ∑' k, w k := hwsumm.sum_le_tsum _ fun k _ => hw k
    _ ≤ 1 := hwsum

/-- Core: strict-alarm bound at level `c` via finite-prefix union. -/
private lemma countable_strict_alarm_le [IsProbabilityMeasure μ]
    (hw : ∀ k, 0 ≤ w k) (hwsumm : Summable w) (hwsum : ∑' k, w k ≤ 1)
    (hE : ∀ k, Supermartingale (E k) 𝒢 μ) (hEnn : ∀ k t ω, 0 ≤ E k t ω)
    (hE0 : ∀ k, μ[E k 0] ≤ 1)
    (hsum : ∀ t ω, Summable fun k => w k * E k t ω)
    {c : ℝ} (hc : 0 < c) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
        c < stitchedMasterCountable w E t ω} ≤ c⁻¹ := by
  -- finite-prefix alarm sets (non-strict threshold, the finite
  -- theorem's shape)
  set C : ℕ → Set Ω := fun K => {ω | ∃ t ∈ Finset.range (n + 1),
    c ≤ ∑ k ∈ Finset.range (K + 1), w k * E k t ω} with hC
  -- each C K is bounded by the finite theorem on Fin (K+1)
  have hCK : ∀ K, μ (C K) ≤ ENNReal.ofReal (c⁻¹) := by
    intro K
    have hfin := stitching_eprocess_anytime
      (w := fun i : Fin (K + 1) => w i)
      (hw := fun i => hw i)
      (hwsum := finsum_w_le w hw hwsumm hwsum K)
      (E := fun i : Fin (K + 1) => E i)
      (hE := fun i => hE i) (hEnn := fun i => hEnn i)
      (hE0 := fun i => hE0 i)
      (hdelta := inv_pos.2 hc) (n := n)
    have hinvc : (c⁻¹)⁻¹ = c := by field_simp
    rw [hinvc] at hfin
    have hset : C K = {ω | ∃ t ∈ Finset.range (n + 1),
        c ≤ stitchedMaster (fun i : Fin (K + 1) => w i)
          (fun i : Fin (K + 1) => E i) t ω} := by
      rw [hC]
      ext ω
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨t, ht, hle⟩
        exact ⟨t, ht, by rw [finMaster_eq w E K t ω]; exact hle⟩
      · rintro ⟨t, ht, hle⟩
        exact ⟨t, ht, by rw [← finMaster_eq w E K t ω]; exact hle⟩
    rw [← hset] at hfin
    rw [measureReal_def] at hfin
    rw [← ENNReal.toReal_le_toReal (by finiteness) (by finiteness),
      ENNReal.toReal_ofReal (le_of_lt (inv_pos.2 hc))]
    exact hfin
  -- C is monotone
  have hmono : Monotone C := by
    intro K K' hKK ω hω
    obtain ⟨t, ht, hle⟩ := hω
    exact ⟨t, ht, le_trans hle (rangeSum_mono w E hw hEnn hKK t ω)⟩
  -- union measure is the supremum
  have hU : μ (⋃ K, C K) ≤ ENNReal.ofReal (c⁻¹) := by
    rw [hmono.measure_iUnion]
    exact iSup_le hCK
  -- strict alarm set is inside the union
  have hsub : {ω | ∃ t ∈ Finset.range (n + 1),
      c < stitchedMasterCountable w E t ω} ⊆ ⋃ K, C K := by
    rintro ω ⟨t, ht, hlt⟩
    obtain ⟨K, hK⟩ := exists_partial_gt (hsum t ω) hlt
    refine Set.mem_iUnion.2 ⟨K, ⟨t, ht, ?_⟩⟩
    have hss : Finset.range K ⊆ Finset.range (K + 1) := by
      intro x hx
      have hx' := Finset.mem_range.1 hx
      exact Finset.mem_range.2 (by omega)
    exact le_trans hK (Finset.sum_le_sum_of_subset_of_nonneg hss
      (fun k _ _ => mul_nonneg (hw k) (hEnn k t ω)))
  -- conclude
  rw [measureReal_def]
  calc (μ {ω | ∃ t ∈ Finset.range (n + 1),
        c < stitchedMasterCountable w E t ω}).toReal
      ≤ (μ (⋃ K, C K)).toReal :=
        ENNReal.toReal_mono (by finiteness) (measure_mono hsub)
    _ ≤ (ENNReal.ofReal (c⁻¹)).toReal := ENNReal.toReal_mono (by finiteness) hU
    _ = c⁻¹ := ENNReal.toReal_ofReal (le_of_lt (inv_pos.2 hc))

/-- Initial mass of the countable master:
`μ[M 0] = ∑' k, w k * μ[E k 0]` (the countable analogue of
`stitching_master_initial_mass`). -/
theorem stitching_countable_initial_mass
    (hw : ∀ k, 0 ≤ w k) (hwsumm : Summable w) (hwsum : ∑' k, w k ≤ 1)
    (hE : ∀ k, Supermartingale (E k) 𝒢 μ) (hEnn : ∀ k ω, 0 ≤ E k 0 ω)
    (hE0 : ∀ k, μ[E k 0] ≤ 1) :
    μ[stitchedMasterCountable w E 0] = ∑' k, w k * μ[E k 0] := by
  have hint : ∀ k, Integrable (fun ω => w k * E k 0 ω) μ :=
    fun k => ((hE k).integrable 0).const_mul (w k)
  have hck : ∀ k, w k * μ[E k 0] ≤ w k := fun k => by
    simpa using mul_le_mul_of_nonneg_left (hE0 k) (hw k)
  have hnnint : ∀ k, 0 ≤ μ[E k 0] := fun k => integral_nonneg fun ω => hEnn k ω
  have hsumwc : Summable fun k => w k * μ[E k 0] :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hw k) (hnnint k)) hck hwsumm
  have hf' : ∑' k, ∫⁻ a, ‖w k * E k 0 a‖ₑ ∂μ ≠ ∞ := by
    have h1 : ∀ k, ∫⁻ a, ‖w k * E k 0 a‖ₑ ∂μ
        = ENNReal.ofReal (w k * μ[E k 0]) := by
      intro k
      rw [← MeasureTheory.ofReal_integral_norm_eq_lintegral_enorm (hint k)]
      congr 1
      have hnn : ∀ a, (‖(w k * E k 0 a : ℝ)‖) = w k * E k 0 a := fun a => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw k) (hEnn k a))]
      rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hnn), integral_const_mul]
    have h2 : ∑' k, ∫⁻ a, ‖w k * E k 0 a‖ₑ ∂μ
        = ENNReal.ofReal (∑' k, w k * μ[E k 0]) := by
      rw [tsum_congr fun k => h1 k,
        ENNReal.ofReal_tsum_of_nonneg
          (fun k => mul_nonneg (hw k) (hnnint k)) hsumwc]
    rw [h2]
    have h3 : ∑' k, w k * μ[E k 0] ≤ 1 :=
      le_trans (Summable.tsum_le_tsum hck hsumwc hwsumm) hwsum
    have h3lt : ENNReal.ofReal (∑' k, w k * μ[E k 0]) < ∞ :=
      lt_of_le_of_lt (ENNReal.ofReal_le_ofReal h3) (by norm_num)
    exact h3lt.ne
  have hMeq : ∀ x, stitchedMasterCountable w E 0 x = ∑' k, w k * E k 0 x :=
    fun x => rfl
  rw [MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hMeq)]
  rw [integral_tsum (fun k => (hint k).1) hf']
  refine tsum_congr fun k => ?_
  exact integral_const_mul (w k) (fun ω => E k 0 ω)

/-- **Countable stitched anytime validity (MAIN)**: a countable
family of nonnegative supermartingales with summable nonnegative
prior weights `∑' w ≤ 1` and pointwise-summable mixture stitches
into a master with the Ville bound `μ.real {∃ t ≤ n, δ⁻¹ ≤ M t} ≤ δ`
uniformly in `n`. Finite-prefix monotone reduction: the alarm set
is sandwiched into the increasing union of finite-master alarm
sets, each bounded by `stitching_eprocess_anytime`. -/
theorem stitching_countable_ville [IsProbabilityMeasure μ]
    (hw : ∀ k, 0 ≤ w k) (hwsumm : Summable w) (hwsum : ∑' k, w k ≤ 1)
    (hE : ∀ k, Supermartingale (E k) 𝒢 μ) (hEnn : ∀ k t ω, 0 ≤ E k t ω)
    (hE0 : ∀ k, μ[E k 0] ≤ 1)
    (hsum : ∀ t ω, Summable fun k => w k * E k t ω)
    {delta : ℝ} (hdelta : 0 < delta) (n : ℕ) :
    μ.real {ω | ∃ t ∈ Finset.range (n + 1),
        delta⁻¹ ≤ stitchedMasterCountable w E t ω} ≤ delta := by
  rcases lt_or_ge delta 1 with hd1 | hd1
  swap
  · calc μ.real {ω | ∃ t ∈ Finset.range (n + 1),
          delta⁻¹ ≤ stitchedMasterCountable w E t ω}
        ≤ μ.real Set.univ :=
          measureReal_mono (Set.subset_univ _) (by finiteness)
      _ = 1 := probReal_univ
      _ ≤ delta := hd1
  · by_contra hcon
    push Not at hcon
    set R := μ.real {ω | ∃ t ∈ Finset.range (n + 1),
        delta⁻¹ ≤ stitchedMasterCountable w E t ω} with hRdef
    rw [hRdef] at hcon
    have hRpos : 0 < R := lt_trans hdelta hcon
    have hR1 : R ≤ 1 := by
      rw [hRdef]
      exact le_trans (measureReal_mono (Set.subset_univ _) (by finiteness))
        (le_of_eq probReal_univ)
    have hinvR : R⁻¹ < delta⁻¹ := (inv_lt_inv₀ hRpos hdelta).2 hcon
    set cp := (delta⁻¹ + R⁻¹) / 2 with hcpdef
    have hcppos : 0 < cp := by
      rw [hcpdef]
      exact div_pos (add_pos (inv_pos.2 hdelta) (inv_pos.2 hRpos)) two_pos
    have hcplt : cp < delta⁻¹ := by rw [hcpdef]; linarith
    have hcpR : R⁻¹ < cp := by rw [hcpdef]; linarith
    have hsub : {ω | ∃ t ∈ Finset.range (n + 1),
        delta⁻¹ ≤ stitchedMasterCountable w E t ω} ⊆
        {ω | ∃ t ∈ Finset.range (n + 1),
          cp < stitchedMasterCountable w E t ω} := by
      rintro ω ⟨t, ht, hle⟩
      exact ⟨t, ht, lt_of_lt_of_le hcplt hle⟩
    have hcore := countable_strict_alarm_le w E hw hwsumm hwsum hE hEnn hE0
      hsum hcppos n
    have hRle : R ≤ cp⁻¹ := by
      rw [hRdef]
      exact le_trans (measureReal_mono hsub (by finiteness)) hcore
    have hcpinv : cp⁻¹ < R := by
      exact (inv_lt_inv₀ hcppos (inv_pos.2 hRpos)).2 hcpR |>.trans_eq
        (inv_inv R)
    linarith

/-- Numeric anchor: the geometric schedule is a countable stitch. -/
theorem stitching_countable_geometric_weights :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = 1 := by
  have hfun : ∀ k : ℕ, ((1 : ℝ) / 2) ^ (k + 1) = (1 / 2) * ((1 : ℝ) / 2) ^ k :=
    fun k => by rw [pow_succ, mul_comm]
  have hsumm : Summable fun k : ℕ => ((1 : ℝ) / 2) ^ k :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  rw [tsum_congr hfun, hsumm.tsum_mul_left, tsum_geometric_two]
  norm_num


end Hagi.Unified

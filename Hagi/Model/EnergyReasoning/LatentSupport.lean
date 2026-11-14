/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Model.EnergyReasoning.LatentEnergy

set_option linter.style.header false

/-!
# Latent fixed point support and reachability

Track B2 (addendum A11 B-level): support/connectivity properties of the
LATENT fixed point `z*` of `latentUpdate` (C272's `LatentEnergy.lean`
carrier, fixed-point equation `z* i = (Σ_{j ∈ N i} z* j + 1[i = G])/m`
with symmetric adjacency, degree bound `(N i).card ≤ Δ`, `m > Δ`).

Main results:

* `latent_fixed_unique` — uniqueness of the fixed point (directly from
  `latent_update_contraction`: `‖z − z'‖ ≤ (Δ/m)·‖z − z'‖` with
  `Δ/m < 1` forces equality), reused by `latent_fixed_zero_off_closed`.
* `latent_fixed_nonneg` — (B2 MAIN) the unique fixed point is
  nonnegative: at the argmin index the goal injection `1[i = G] ≥ 0`
  and the neighbour terms give `m·z i ≥ card(N i)·z i`, so
  `(m − card(N i))·z i ≥ 0` with `m > Δ ≥ card` forces `z i ≥ 0`.
* `latent_fixed_goal_pos` — the goal source term: `1/m ≤ z* G`.
* `latent_fixed_ge_of_neighbour` — propagation across an edge:
  `i ∈ N j → z* j / m ≤ z* i` (symmetry is load-bearing: it puts `j`
  into `N i`; nonnegativity handles the remaining neighbour terms).
* `LatentPath` — inductive reachability from the goal over the
  neighbour relation (path length = number of edges).
* `latent_fixed_pos_of_reachable` — (B2 MAIN) if `LatentPath N G i k`
  then `(1/m)^(k+1) ≤ z* i`, in particular `0 < z* i`: positivity
  propagates from the goal along every path.
* `latent_fixed_upper_bound` — global sup bound `z* i ≤ 1/(m − Δ)`
  (argmax mirror of the nonneg argument).
* `latent_fixed_zero_off_closed` — (B2 MAIN) on a set `C'` closed
  under neighbours (`∀ i ∈ C', N i ⊆ C'`) with no goal
  (`∀ i ∈ C', i ≠ G`), the fixed point vanishes: the 0-on-C' patch of
  `z*` is again a fixed point (closedness for `i ∈ C'`; SYMMETRY for
  `i ∉ C'` — a neighbour in `C'` would pull `i` into `C'`), and
  `latent_fixed_unique` forces it back onto `z*`.

## Honest boundaries

* NO per-distance DECAY upper bound (`z* i ≤ z_G/m^k · const`) is
  claimed: it needs graph structure beyond degree boundedness (`z i`
  receives contributions from ALL its neighbours, so off-path edges
  break a pure path-decay bound). The provable general statement is
  the global sup bound `1/(m − Δ)` (see `latent_fixed_upper_bound`);
  the name `latent_fixed_decay_upper` is nonexistent (RootApi negative
  pin). Honesty over completeness.
* All theorems are about the FIXED POINT of `latentUpdate` (which
  exists uniquely by C272's Banach theorem); no iterate statements are
  duplicated here (see `latent_iterate_err_bound` there).

Numeric anchor (consumed from `LatentEnergy.lean`'s frozen fixture):
`zstar4 = ![21/55, 8/55, 3/55, 1/55]` on the `Fin 4` path with
`m = 3`, `G = 0`: all entries positive, `(1/3)^4 = 1/81 ≤ 1/55`
(reachability at distance 3), `21/55 ≤ 1 = 1/(3 − 2)` (upper bound).
-/

namespace Hagi.Model.EnergyReasoning

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Uniqueness and nonnegativity -/
section Support

/-- **`latent_fixed_unique`** — two fixed points of the latent update
coincide (direct consequence of the C272 ℓ∞ contraction
`latent_update_contraction` with factor `Δ/m < 1`). -/
theorem latent_fixed_unique (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (z z' : ι → ℝ)
    (hz : latentUpdate N m G z = z) (hz' : latentUpdate N m G z' = z') : z = z' := by
  by_contra hne
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have h := latent_update_contraction N m G hΔ hm z z'
  rw [hz, hz'] at h
  have h0 : 0 < ‖z - z'‖ := norm_pos_iff.mpr (fun h0 => hne (sub_eq_zero.mp h0))
  have hlt : ((Δ : ℝ) / m) * ‖z - z'‖ < ‖z - z'‖ := by
    have e : ((Δ : ℝ) / m) * ‖z - z'‖ < (m / m) * ‖z - z'‖ :=
      mul_lt_mul_of_pos_right (div_lt_div_iff_of_pos_right hm0 |>.mpr (by linarith)) h0
    rw [div_self (ne_of_gt hm0), one_mul] at e
    exact e
  linarith

/-- **`latent_fixed_nonneg`** — (B2 MAIN) with `m > Δ`, any fixed point
of the latent update is nonnegative (minimum argument: at the argmin
index `m·z i = Σ_{N i} z j + 1[i = G] ≥ card(N i)·z i`, and
`m − card(N i) > 0` since `card ≤ Δ < m`). -/
theorem latent_fixed_nonneg (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ i, 0 ≤ zstar i := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hile⟩ := Finset.exists_min_image Finset.univ zstar ⟨i₀, by simp⟩
  have hmin : ∀ j, zstar i ≤ zstar j := fun j => hile j (Finset.mem_univ j)
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfix : zstar i = (∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0)) / m :=
    (congrFun hz i).symm
  have hsumge : ((N i).card : ℝ) * zstar i ≤ ∑ j ∈ N i, zstar j := by
    have e1 : ∑ j ∈ N i, zstar i = ((N i).card : ℝ) * zstar i := by
      rw [Finset.sum_const]; simp
    calc ((N i).card : ℝ) * zstar i = ∑ j ∈ N i, zstar i := e1.symm
      _ ≤ ∑ j ∈ N i, zstar j := Finset.sum_le_sum fun j _ => hmin j
  have hind : (0:ℝ) ≤ (if i = G then (1:ℝ) else 0) := by split <;> norm_num
  have hkey : ((N i).card : ℝ) * zstar i ≤ m * zstar i := by
    have e : m * zstar i = ∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0) := by
      rw [hfix]; exact mul_div_cancel₀ _ (ne_of_gt hm0)
    linarith
  have hzineg : zstar i < 0 := lt_of_le_of_lt (hmin i₀) hi₀
  have hpos : (0:ℝ) < m - (N i).card := by
    have hcard : ((N i).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ i
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfinal : (0:ℝ) ≤ m * zstar i - ((N i).card : ℝ) * zstar i := by linarith
  have hznn : (0:ℝ) ≤ zstar i := by
    have e : m * zstar i - ((N i).card : ℝ) * zstar i
        = (m - ((N i).card : ℝ)) * zstar i := by ring
    rw [e] at hfinal
    exact (mul_nonneg_iff_of_pos_left hpos).mp hfinal
  exact absurd hzineg (not_lt.mpr hznn)

/-- **`latent_fixed_goal_pos`** — the goal source term: `1/m ≤ z* G`
(the fixed-point equation at `G` reads `m·z* G = Σ_{N G} z* j + 1`). -/
theorem latent_fixed_goal_pos (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    1 / m ≤ zstar G := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfix : zstar G = (∑ j ∈ N G, zstar j + (if G = G then (1:ℝ) else 0)) / m :=
    (congrFun hz G).symm
  have e : zstar G = (∑ j ∈ N G, zstar j + 1) / m := by
    rw [hfix]; congr 1; simp
  rw [e, le_div_iff₀ hm0]
  have hsum : (0:ℝ) ≤ ∑ j ∈ N G, zstar j :=
    Finset.sum_nonneg fun j _ => latent_fixed_nonneg N m G hΔ hm zstar hz j
  have hone : (1:ℝ) / m * m = 1 := by field_simp
  linarith

end Support

/-! ## Neighbour propagation and reachability -/
section Reach

/-- **`latent_fixed_ge_of_neighbour`** — propagation across an edge:
`i ∈ N j → z* j / m ≤ z* i`. Symmetry is load-bearing (it puts `j`
into `N i`); nonnegativity handles the remaining neighbour terms. -/
theorem latent_fixed_ge_of_neighbour (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar)
    {i j : ι} (hn : i ∈ N j) : zstar j / m ≤ zstar i := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  have hfix : zstar i = (∑ j' ∈ N i, zstar j' + (if i = G then (1:ℝ) else 0)) / m :=
    (congrFun hz i).symm
  have hn' : j ∈ N i := (hNsymm j i).mp hn
  have hnn : ∀ j', (0:ℝ) ≤ zstar j' := latent_fixed_nonneg N m G hΔ hm zstar hz
  have hge : zstar j ≤ ∑ j' ∈ N i, zstar j' :=
    Finset.single_le_sum (f := zstar) (fun j' _ => hnn j') hn'
  have hind : (0:ℝ) ≤ (if i = G then (1:ℝ) else 0) := by split <;> norm_num
  rw [hfix, le_div_iff₀ hm0]
  have hjm : zstar j / m * m = zstar j := by field_simp
  linarith

/-- **`LatentPath`** — inductive reachability from the goal `G` over
the neighbour relation; the ℕ index is the path length (number of
edges). -/
inductive LatentPath (N : ι → Finset ι) (G : ι) : ι → ℕ → Prop
  | goal : LatentPath N G G 0
  | step {j i : ι} {k : ℕ} (h : LatentPath N G j k) (hn : i ∈ N j) :
      LatentPath N G i (k + 1)

/-- **`latent_fixed_pos_of_reachable`** — (B2 MAIN) if `i` is reachable
from the goal by a path of length `k`, then `(1/m)^(k+1) ≤ z* i`; in
particular `0 < z* i`: positivity propagates from the goal source term
along every path. -/
theorem latent_fixed_pos_of_reachable (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ {i k}, LatentPath N G i k → (1 / m) ^ (k + 1) ≤ zstar i := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  intro i k hp
  induction hp with
  | goal =>
      simpa using latent_fixed_goal_pos N m G hΔ hm zstar hz
  | @step j i k h hn ih =>
      have h1 := latent_fixed_ge_of_neighbour N m G hNsymm hΔ hm zstar hz hn
      have hexp : (1 / m) ^ (k + 1 + 1) = (1 / m) ^ (k + 1) / m := by
        rw [pow_succ]; field_simp
      rw [hexp, div_le_iff₀ hm0]
      have h2 : m * (zstar j / m) = zstar j := by field_simp
      calc (1 / m) ^ (k + 1) ≤ zstar j := ih
        _ = m * (zstar j / m) := h2.symm
        _ ≤ m * zstar i := mul_le_mul_of_nonneg_left h1 (le_of_lt hm0)
        _ = zstar i * m := by ring

/-- **`latent_fixed_upper_bound`** — global sup bound: every entry of
the fixed point obeys `z* i ≤ 1/(m − Δ)` (argmax mirror of the
nonneg argument: `m·z_max = Σ + 1[i = G] ≤ Δ·z_max + 1`). This is the
provable general upper statement; a per-distance decay bound needs
graph structure beyond degree boundedness and is NOT claimed. -/
theorem latent_fixed_upper_bound (N : ι → Finset ι) (m : ℝ) (G : ι)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ i, zstar i ≤ 1 / (m - (Δ : ℝ)) := by
  have hm0 : 0 < m := by
    have : (0:ℝ) ≤ (Δ : ℝ) := Nat.cast_nonneg _; linarith
  by_contra hcon
  push_neg at hcon
  obtain ⟨i₀, hi₀⟩ := hcon
  obtain ⟨i, -, hile⟩ := Finset.exists_max_image Finset.univ zstar ⟨i₀, by simp⟩
  have hmax : ∀ j, zstar j ≤ zstar i := fun j => hile j (Finset.mem_univ j)
  have hfix : zstar i = (∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0)) / m :=
    (congrFun hz i).symm
  have hcard : ((N i).card : ℝ) ≤ (Δ : ℝ) := by exact_mod_cast hΔ i
  have hsumle : ∑ j ∈ N i, zstar j ≤ ((N i).card : ℝ) * zstar i := by
    have e1 : ∑ j ∈ N i, zstar i = ((N i).card : ℝ) * zstar i := by
      rw [Finset.sum_const]; simp
    calc ∑ j ∈ N i, zstar j ≤ ∑ j ∈ N i, zstar i :=
          Finset.sum_le_sum fun j _ => hmax j
      _ = ((N i).card : ℝ) * zstar i := e1
  have hind : (if i = G then (1:ℝ) else 0) ≤ 1 := by split <;> norm_num
  have e : m * zstar i = ∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0) := by
    rw [hfix]; exact mul_div_cancel₀ _ (ne_of_gt hm0)
  have hviol : 1 / (m - (Δ:ℝ)) < zstar i := lt_of_lt_of_le hi₀ (hmax i₀)
  have hgap : (0:ℝ) < m - (Δ : ℝ) := by linarith
  have hnnz : (0:ℝ) ≤ zstar i := latent_fixed_nonneg N m G hΔ hm zstar hz i
  have hcz : ((N i).card : ℝ) * zstar i ≤ ((Δ:ℝ)) * zstar i :=
    mul_le_mul_of_nonneg_right hcard hnnz
  have h1 : ∑ j ∈ N i, zstar j + (if i = G then (1:ℝ) else 0)
      ≤ ((Δ:ℝ)) * zstar i + 1 := by linarith
  have hle : (m - (Δ:ℝ)) * zstar i ≤ 1 := by nlinarith [e, h1]
  have hone : (m - (Δ:ℝ)) * (1 / (m - (Δ:ℝ))) = 1 := by field_simp
  have hlt : (m - (Δ:ℝ)) * (1 / (m - (Δ:ℝ))) < (m - (Δ:ℝ)) * zstar i :=
    mul_lt_mul_of_pos_left hviol hgap
  rw [hone] at hlt
  linarith

end Reach

/-! ## Zero on neighbour-closed goal-free regions -/
section Closed

/-- **`latent_fixed_zero_off_closed`** — (B2 MAIN) if `C'` is closed
under neighbours (`∀ i ∈ C', N i ⊆ C'`) and carries no goal
(`∀ i ∈ C', i ≠ G`), then the fixed point vanishes on `C'`: the
0-on-`C'` patch of `z*` is again a fixed point (closedness for
`i ∈ C'`; SYMMETRY for `i ∉ C'` — a neighbour in `C'` would pull `i`
into `C'`), and `latent_fixed_unique` forces it back onto `z*`. -/
theorem latent_fixed_zero_off_closed (N : ι → Finset ι) (m : ℝ) (G : ι)
    (hNsymm : ∀ i j, j ∈ N i ↔ i ∈ N j)
    {Δ : ℕ} (hΔ : ∀ i, (N i).card ≤ Δ) (hm : (Δ : ℝ) < m)
    (C' : Finset ι)
    (hC : ∀ i ∈ C', N i ⊆ C') (hG : ∀ i ∈ C', i ≠ G)
    (zstar : ι → ℝ) (hz : latentUpdate N m G zstar = zstar) :
    ∀ i ∈ C', zstar i = 0 := by
  set z' : ι → ℝ := fun i => if i ∈ C' then 0 else zstar i with hz'def
  have hfixz' : latentUpdate N m G z' = z' := by
    funext i
    by_cases hmem : i ∈ C'
    · have hsub : ∀ j ∈ N i, z' j = 0 := by
        intro j hj
        simp [hz'def, hC i hmem hj]
      have hsum : ∑ j ∈ N i, z' j = 0 := Finset.sum_eq_zero hsub
      have hind : (if i = G then (1:ℝ) else 0) = 0 := by simp [hG i hmem]
      show (∑ j ∈ N i, z' j + (if i = G then (1:ℝ) else 0)) / m = z' i
      rw [hsum, hind]
      simp [hz'def, hmem]
    · have hnot : ∀ j ∈ N i, z' j = zstar j := by
        intro j hj
        have hnc : j ∉ C' := by
          intro hc
          exact hmem ((hC j hc) ((hNsymm i j).mp hj))
        simp [hz'def, hnc]
      show (∑ j ∈ N i, z' j + (if i = G then (1:ℝ) else 0)) / m = z' i
      have hsum' : ∑ j ∈ N i, z' j = ∑ j ∈ N i, zstar j :=
        Finset.sum_congr rfl hnot
      have hzi : z' i = zstar i := by rw [hz'def]; simp [hmem]
      rw [hsum', hzi]
      exact congrFun hz i
  have heq : z' = zstar := latent_fixed_unique N m G hΔ hm z' zstar hfixz' hz
  intro i hi
  have hz'i : z' i = 0 := by simp [hz'def, hi]
  rw [← heq]
  exact hz'i

end Closed

/-! ## Fixtures and numeric anchors -/
section Fixture

/-- Numeric anchor: every entry of the frozen path-graph fixed point
`zstar4 = ![21/55, 8/55, 3/55, 1/55]` is strictly positive. -/
example : ∀ i, (0:ℝ) < zstar4 i := by
  intro i; fin_cases i <;> norm_num [zstar4]

/-- Numeric anchor (reachability): cell `3` at path distance `3` from
the goal `0` obeys `(1/3)^(3+1) = 1/81 ≤ 1/55 = zstar4 3`. -/
example : (1:ℝ) / 3 ^ (3+1) ≤ zstar4 3 := by norm_num [zstar4]

/-- Numeric anchor (upper bound): `zstar4 0 = 21/55 ≤ 1 = 1/(3 − 2)`
(`m = 3`, `Δ = 2`). -/
example : zstar4 0 ≤ 1 / (3 - (2:ℝ)) := by norm_num [zstar4]

/-- **`emptyN2`** — empty-adjacency `Fin 2` fixture (zero-off-closed
anchor). -/
def emptyN2 : Fin 2 → Finset (Fin 2) := fun _ => ∅

/-- **`zstar2`** — the unique fixed point of the empty-adjacency update
with `m = 3`, `G = 0`: `![1/3, 0]` (cell `1` is unreachable and lies in
the closed goal-free region `{1}`). -/
noncomputable def zstar2 : Fin 2 → ℝ := fun i => if i = 0 then (1:ℝ)/3 else 0

/-- Numeric anchor: `zstar2` solves the fixed-point equation. -/
example : latentUpdate emptyN2 3 0 zstar2 = zstar2 := by
  funext i; fin_cases i <;> simp [latentUpdate, emptyN2, zstar2]

/-- Numeric anchor (zero-off-closed): on the closed goal-free region
`C' = {1}` the fixed point vanishes. -/
example : ∀ i ∈ ({1} : Finset (Fin 2)), zstar2 i = 0 := by
  have hsymm : ∀ i j, j ∈ emptyN2 i ↔ i ∈ emptyN2 j := by
    intro i j; fin_cases i <;> fin_cases j <;> simp [emptyN2]
  have hΔ : ∀ i, (emptyN2 i).card ≤ 0 := by
    intro i; fin_cases i <;> simp [emptyN2]
  have hC : ∀ i ∈ ({1} : Finset (Fin 2)), emptyN2 i ⊆ {1} := by
    intro i hi
    have hi1 : i = 1 := by simpa [Finset.mem_singleton] using hi
    rw [hi1]; simp [emptyN2]
  have hG : ∀ i ∈ ({1} : Finset (Fin 2)), i ≠ 0 := by
    intro i hi
    have hi1 : i = 1 := by simpa [Finset.mem_singleton] using hi
    rw [hi1]; simp
  have hfix : latentUpdate emptyN2 3 0 zstar2 = zstar2 := by
    funext i; fin_cases i <;> simp [latentUpdate, emptyN2, zstar2]
  intro i hi
  exact latent_fixed_zero_off_closed emptyN2 3 0 hsymm hΔ (by norm_num) {1}
    hC hG zstar2 hfix i hi

end Fixture

end Hagi.Model.EnergyReasoning

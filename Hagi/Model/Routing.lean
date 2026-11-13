/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Prelude.InfoCore

/-!
# Routing dynamics: softmax odds-ratchet, deadlock witness

B6 lane ("Stuck in a Loop", Eyler et al. 2026-09-09, addendum A3):
the exact algebraic core of router lock-in and its failure mode.

1. `softDef_odds` — EXACT odds-ratio update of softmax under an
   arbitrary score shift: a⁺j/a⁺k = (aj/ak)·exp(Δsj − Δsk).
2. `odds_ratchet` — one-step local lock-in: a score shift
   proportional to the attention row itself (Δs = c·a, c > 0)
   strictly increases the odds of a higher-attention key against a
   lower one. Single step, exact; NO global/iterated growth claim.
3. `ratchet_advantage_step` / `ratchet_advantage_mono` — exact
   V-step identity on `Fin d → ℝ`: with per-key value update
   v⁺j = vj − η·aj·δ the advantage Aj = −⟪δ, vj − y⟫ updates as
   A⁺j = Aj + η·aj·‖δ‖² ≥ Aj: every attended key gains advantage.
4. `deadlock_witness` — 3-key exact-rational NEGATIVE witness: the
   useful key carries attention exactly ε = 1/10, so its
   query-gradient contribution has norm ≤ ε·M — useful-but-ignored
   keys train the query slowly (the deadlock the anti-lock-in bound
   in `Hagi.Autonomy.HedgeSurvivor.ewNorm_survivor_lower` guards
   against).

Reference search: no existing softmax odds-update or attention
ratchet formalization in this repo or the pinned Mathlib snapshot
(56a005855ea17e0b0958f73ec801ae140b0a1679); constructions are
elementary ordered-field + `Real.exp` algebra.
-/

set_option relaxedAutoImplicit false

open Hagi.Prelude

namespace Hagi.Model.Routing

variable {κ : Type*} [Fintype κ] [Nonempty κ]

/-! ## Exact odds-ratio update -/

/-- Softmax odds update under an arbitrary score shift `ds`:
EXACT, no first-order approximation —
`a⁺j / a⁺k = (aj / ak) · exp (ds j - ds k)`. -/
theorem softDef_odds (s ds : κ → ℝ) (j k : κ) :
    softDef (fun x => s x + ds x) j / softDef (fun x => s x + ds x) k
      = (softDef s j / softDef s k) * Real.exp (ds j - ds k) := by
  have hZ : 0 < ∑ b, Real.exp (s b + ds b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  have hZ' : 0 < ∑ b, Real.exp (s b) :=
    Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty
  unfold softDef
  show (Real.exp (s j + ds j) / ∑ b, Real.exp (s b + ds b))
      / (Real.exp (s k + ds k) / ∑ b, Real.exp (s b + ds b)) = _
  have hZne : (∑ b, Real.exp (s b + ds b)) ≠ 0 := hZ.ne'
  have hZne' : (∑ b, Real.exp (s b)) ≠ 0 := hZ'.ne'
  have e1 : (Real.exp (s j + ds j) / ∑ b, Real.exp (s b + ds b))
      / (Real.exp (s k + ds k) / ∑ b, Real.exp (s b + ds b))
      = Real.exp (s j + ds j) / Real.exp (s k + ds k) := by
    field_simp
  have e2 : (Real.exp (s j) / ∑ b, Real.exp (s b))
      / (Real.exp (s k) / ∑ b, Real.exp (s b))
      = Real.exp (s j) / Real.exp (s k) := by
    field_simp
  rw [e1, e2, ← Real.exp_sub, ← Real.exp_sub, ← Real.exp_add]
  congr 1
  ring

/-! ## Local ratchet (odds form) -/

/-- ONE-STEP local ratchet, exact: if the score shift is
proportional to the attention row itself (Δs = c·a, a = `softDef s`,
c > 0), then the odds of a higher-attention key against a
lower-attention one strictly increase (multiplicative factor
`exp (c * (a j - a k)) > 1`). Single step only — no global or
iterated growth is claimed. -/
theorem odds_ratchet (s : κ → ℝ) (c : ℝ) (hc : 0 < c) (j k : κ)
    (hjk : softDef s k < softDef s j) :
    softDef s j / softDef s k
      < softDef (fun x => s x + c * softDef s x) j
        / softDef (fun x => s x + c * softDef s x) k := by
  have hexp : (1:ℝ)
      < Real.exp (c * softDef s j - c * softDef s k) := by
    rw [Real.one_lt_exp_iff]
    nlinarith [mul_pos hc (show 0 < softDef s j - softDef s k by linarith)]
  have hpos : 0 < softDef s j / softDef s k :=
    div_pos (softDef_pos s j) (softDef_pos s k)
  conv_rhs => rw [softDef_odds s (fun x => c * softDef s x) j k]
  exact lt_mul_of_one_lt_right hpos hexp

/-! ## Exact V-step advantage identity (ratchet value core) -/

variable {d : ℕ}

/-- Per-key value update: key `j` receives gradient `a j • δ`
(the exact B2 identity `grad_v = a·δ`, taken here as the definition
of the V-step). -/
noncomputable def vstep (v : κ → Fin d → ℝ) (a : κ → ℝ) (eta : ℝ)
    (delta : Fin d → ℝ) (j : κ) : Fin d → ℝ :=
  fun i => v j i - eta * a j * delta i

/-- Advantage of key `j` for prediction error `δ` and target `y`:
`A j = -∑ i, δ i * (v j i - y i)` (inner product as an explicit
sum). -/
noncomputable def adv (v : κ → Fin d → ℝ) (delta y : Fin d → ℝ)
    (j : κ) : ℝ := -(∑ i, delta i * (v j i - y i))

omit [Fintype κ] [Nonempty κ] in
/-- EXACT ratchet identity: after the V-step with rate η, the
advantage of every key updates as
`A⁺j = Aj + η * a j * ‖δ‖²` (with `‖δ‖²` as an explicit sum of
squares). -/
theorem ratchet_advantage_step (v : κ → Fin d → ℝ) (a : κ → ℝ)
    (eta : ℝ) (delta y : Fin d → ℝ) (j : κ) :
    adv (vstep v a eta delta) delta y j
      = adv v delta y j + eta * a j * (∑ i, delta i * delta i) := by
  have hexpand : ∑ i, delta i * ((v j i - eta * a j * delta i) - y i)
      = (∑ i, delta i * (v j i - y i))
        - eta * a j * (∑ i, delta i * delta i) := by
    have h : ∀ i, delta i * ((v j i - eta * a j * delta i) - y i)
        = delta i * (v j i - y i) - eta * a j * (delta i * delta i) :=
      fun i => by ring
    calc ∑ i, delta i * ((v j i - eta * a j * delta i) - y i)
        = ∑ i, (delta i * (v j i - y i)
            - eta * a j * (delta i * delta i)) :=
          Finset.sum_congr rfl (fun x _ => h x)
      _ = (∑ i, delta i * (v j i - y i))
          - eta * a j * (∑ i, delta i * delta i) := by
          rw [Finset.sum_sub_distrib, Finset.mul_sum]
  unfold adv vstep
  rw [hexpand]
  ring

omit [Fintype κ] [Nonempty κ] in
/-- Monotone form: with `η ≥ 0` and nonnegative attention, the
advantage of a key never decreases under the V-step — the
value-level half of the ratchet (the score-level half is
`odds_ratchet`). -/
theorem ratchet_advantage_mono (v : κ → Fin d → ℝ) (a : κ → ℝ)
    (eta : ℝ) (delta y : Fin d → ℝ) (j : κ)
    (heta : 0 ≤ eta) (hnn : 0 ≤ a j) :
    adv v delta y j ≤ adv (vstep v a eta delta) delta y j := by
  rw [ratchet_advantage_step v a eta delta y j]
  have hsq : 0 ≤ ∑ i, delta i * delta i :=
    Finset.sum_nonneg fun i _ => mul_self_nonneg (delta i)
  linarith [mul_nonneg (mul_nonneg heta hnn) hsq]

/-! ## Deadlock witness: exact rational softmax -/

/-- Scores realizing the attention row `[1/10, 9/20, 9/20]` on
`Fin 3`: `s = log a`, so `softDef s = a` exactly (`exp ∘ log`
cancels). -/
noncomputable def dwScores : Fin 3 → ℝ :=
  ![Real.log (1/10), Real.log (9/20), Real.log (9/20)]

theorem dw_att0 : softDef dwScores 0 = 1 / 10 := by
  unfold softDef dwScores
  norm_num [Fin.sum_univ_three, Real.exp_log]

theorem dw_att1 : softDef dwScores 1 = 9 / 20 := by
  unfold softDef dwScores
  norm_num [Fin.sum_univ_three, Real.exp_log]

/-- DEADLOCK WITNESS (negative pinned challenge). Key 0 is the
useful key (advantage scale `M`), but its attention is exactly
ε = 1/10. The query-gradient contribution of key 0 — the exact B2
term `a j • (A j • k j)` — has norm at most ε·M whenever every key
coordinate is bounded by 1: however large the advantage, the query
learns from this key at speed at most ε·M. (A per-coordinate /√d
rescaling is absorbed by the coordinate bound `|k0 i| ≤ 1`.) -/
theorem deadlock_witness (M : ℝ) (hM : 0 ≤ M) (A0 : ℝ) (hA0 : |A0| ≤ M)
    (k0 : Fin d → ℝ) (hk0 : ∀ i, |k0 i| ≤ 1) :
    ‖(fun i => softDef dwScores 0 * (A0 * k0 i))‖ ≤ (1/10) * M := by
  have hnn : (0:ℝ) ≤ (1/10) * M := by positivity
  have hle : ∀ i, |softDef dwScores 0 * (A0 * k0 i)| ≤ (1/10) * M := by
    intro i
    rw [dw_att0, abs_mul, abs_mul,
      abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1/10)]
    have h2 : |A0| * |k0 i| ≤ M * 1 :=
      mul_le_mul hA0 (hk0 i) (abs_nonneg _) hM
    nlinarith
  exact pi_norm_le_iff_of_nonneg hnn |>.2 fun i => by
    simpa [Real.norm_eq_abs] using hle i

end Hagi.Model.Routing

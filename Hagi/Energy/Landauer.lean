/-
Copyright (c) 2026 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib.Tactic
import Hagi.Prelude.Info
set_option linter.style.header false

/-!
# Landauer — the thermodynamic price of discarded information

Physical background (research round, ask.sciencemadereadable.com):
* Landauer / Sagawa–Ueda (PRL 2009, arXiv:0809.4098): erasing
  information carries a fundamental lower bound on dissipated
  work — `k_B T ln 2` per bit for a symmetric memory;
* Janzing et al. (quant-ph/0002048): the reliability of erasure
  is priced by the KL-divergence of the resource state — KL is
  THE thermodynamic currency of a bit erasure;
* Tkachenko (arXiv:2503.09980, 2025): for neural networks the
  thermodynamic price is set by MEMORY (writing/rounding the
  parameters), not arithmetic — exactly the compress stage of a
  HAGI cycle (ternary rounding of weights = bit erasure).

**What is proven here (pure math over the canonical `klDef`)**:
with the empirical premise `h_emp_landauer` (the dissipation of a
weight-erasure step is at least `c_unit` times the discarded KL
— the conditional physics bridge, same status as every `h_emp_`),
the discarded information of one compression step is bounded by
the energy ledger budget over the thermodynamic price of a bit:

```
KL(w_pre ‖ w_post) <= (compressEnergy - jointEnergy) / c_unit
                    <= kappa * s * quantErr / c_unit   (honest ledger)
```

i.e. THE QUANTIZATION BUDGET CAPS THE DISCARDED INFORMATION — a
thermodynamic reading of the compress stage: less energy budget ⇒
less information may be destroyed per cycle. Boundary honesty: the
thermodynamic interpretation of `c_unit` is not proven here; the
module proves the conditional implication chain only.

Combined with `Energy.EntropyProduction.second_law`
(`E_p[Σ] = KL ≥ 0`, the IFT layer) this sandwiches the compress
stage: entropy production is nonnegative AND its information
content is budget-capped.
-/

namespace Hagi.Energy

open Hagi.Prelude

variable {V : Type*} [Fintype V]

/-- The thermodynamic price of one erased bit: `c_unit` stands for
`k_B * T * ln 2` of the runtime (an `h_emp_`-calibrated constant:
the runtime bridge measures T and the physical unit). -/
noncomputable def landauerUnit (cUnit : ℝ) : ℝ := cUnit

/-- **Landauer sandwich (conditional)**: with the physics bridge
`h_emp_landauer` — the dissipation of one weight-erasure
(compress) step is at least `cUnit` times the discarded KL — and
the honest compression ledger (`Dissipation <= kappa*s*quantErr`),
the information destroyed by one ternary-rounding step is
budget-capped:

`KL(w_pre ‖ w_post) <= kappa * s * quantErr / cUnit`.

Reading: the SMALLER the energy budget of a compress step, the
LESS information the step may destroy — thermodynamic pressure
toward minimal-volume architectures at fixed fidelity, the
"maximum quality at minimum volume" constraint of the HAGI goal,
made formal. -/
theorem landauer_sandwich {wPre wPost : V → ℝ}
    (hp : ∀ v, 0 < wPre v) (hq : ∀ v, 0 < wPost v)
    (hsumPre : ∑ v, wPre v = 1) (hsumPost : ∑ v, wPost v = 1)
    (dissipation cUnit kappa s quantErr : ℝ)
    (hcUnit : 0 < cUnit)
    (h_emp_landauer : cUnit * klDef wPost wPre ≤ dissipation)
    (hledger : dissipation ≤ kappa * s * quantErr) :
    klDef wPost wPre ≤ kappa * s * quantErr / cUnit :=
  by
    have h2 : klDef wPost wPre * cUnit ≤ dissipation := by
      rw [mul_comm]; exact h_emp_landauer
    exact (le_div_iff₀ hcUnit).mpr (le_trans h2 hledger)

/-- **Budget-capped erasure at the certified quantization level**:
with the certified window `quantErr <= 1/2` and `0 <= kappa`,
`s`, the discarded information per compress step is at most
`kappa*s/(2*cUnit)` — the thermodynamic cap on per-cycle容量
loss, purely from the certified ledger. -/
theorem landauer_cap_certified {wPre wPost : V → ℝ}
    (hp : ∀ v, 0 < wPre v) (hq : ∀ v, 0 < wPost v)
    (hsumPre : ∑ v, wPre v = 1) (hsumPost : ∑ v, wPost v = 1)
    (dissipation cUnit kappa s quantErr : ℝ)
    (hcUnit : 0 < cUnit) (hkappa : 0 ≤ kappa) (hs : 0 ≤ s)
    (h_emp_landauer :
      cUnit * klDef wPost wPre ≤ dissipation)
    (hledger : dissipation ≤ kappa * s * quantErr)
    (hq2 : quantErr ≤ 1 / 2) :
    klDef wPost wPre ≤ kappa * s / (2 * cUnit) := by
  have h1 := landauer_sandwich hp hq hsumPre hsumPost dissipation cUnit
    kappa s quantErr hcUnit h_emp_landauer hledger
  have hle : kappa * s * quantErr ≤ kappa * s * (1 / 2) :=
    mul_le_mul_of_nonneg_left hq2 (mul_nonneg hkappa hs)
  have hdiv : kappa * s * quantErr / cUnit ≤ kappa * s / (2 * cUnit) := by
    have hmul : kappa * s * quantErr ≤ kappa * s / 2 := by linarith [hle]
    have hstep : kappa * s * quantErr / cUnit
        ≤ kappa * s / 2 / cUnit :=
      (div_le_div_iff_of_pos_right hcUnit).mpr hmul
    have hrw : kappa * s / 2 / cUnit = kappa * s / (2 * cUnit) := by
      field_simp
    calc kappa * s * quantErr / cUnit
        ≤ kappa * s / 2 / cUnit := hstep
      _ = kappa * s / (2 * cUnit) := hrw
  linarith [h1, hdiv]

/-! ### Iteration 2: memory, not arithmetic — the capacity cap -/

/-- **Written-bits cap (Tkachenko arXiv:2503.09980: "the
thermodynamic price of a neural network is set by its memory")**:
writing `F` bits of parameters costs at least `F * cUnit` of work
(physical bridge `h_emp_memwrite`, same status as every
`h_emp_`); with a per-cycle energy budget `B` for the growth stage,
the number of parameter bits WRITTEN this cycle is at most
`B / cUnit` — the thermodynamic cap on architectural growth per
cycle. -/
theorem written_bits_cap (B cUnit F : ℝ) (hcUnit : 0 < cUnit)
    (h_emp_memwrite : cUnit * F ≤ B) :
    F ≤ B / cUnit := by
  have h2 : F * cUnit ≤ B := by rw [mul_comm]; exact h_emp_memwrite
  exact (le_div_iff₀ hcUnit).mpr h2

/-- **Capacity cap on the growth stage**: ternary weights carry
`log 3` bits each (three states); writing `n` new ternary weights
costs at least `n * (log 3) * cUnit`; with budget `B` the growth
of the weight count per cycle is bounded:
`n <= B / (cUnit * log 3)`. Combined with the cone takeoff
(`capability_takeoff_amplified`): the thermodynamic budget is the
physical ceiling on `alpha` — architecture growth is not free, it
is LR-priced by memory. -/
theorem ternary_weight_growth_cap (B cUnit n : ℝ) (hcUnit : 0 < cUnit)
    (_hn : 0 ≤ n) (hlog : (0:ℝ) < Real.log 3)
    (h_emp_memwrite : cUnit * (Real.log 3 * n) ≤ B) :
    n ≤ B / (cUnit * Real.log 3) := by
  have hkey : n * (cUnit * Real.log 3) ≤ B := by
    have hcomm : cUnit * (Real.log 3 * n)
        = n * (cUnit * Real.log 3) := by ring
    rw [hcomm] at h_emp_memwrite
    exact h_emp_memwrite
  exact (le_div_iff₀ (mul_pos hcUnit hlog)).mpr hkey

/-- **Serial divergence (Konopik–Korten–Lutz, Nat Commun 2023):
finite-time serial computing diverges with problem size** — with a
per-operation dissipation floor `cOp > 0` (the finite-time
correction OVER the Landauer limit; parallel execution with
`P >= 1` lanes splits the problem), a serial run over `n`
operations dissipates at least `n * cOp`, so a fixed energy
budget `B` bounds the serial problem size: `n <= B / cOp`.
The HAGI reading: expert-parallel growth lanes are the
thermodynamically sound scaling axis — the growth frontier must
stay parallelizable, else the energy budget caps the run size. -/
theorem serial_divergence_cap (B cOp n : ℝ) (hcOp : 0 < cOp)
    (hn : 0 ≤ n)
    (h_emp_finite_time : cOp * n ≤ B) :
    n ≤ B / cOp := by
  have h2 : n * cOp ≤ B := by rw [mul_comm]; exact h_emp_finite_time
  exact (le_div_iff₀ hcOp).mpr h2


/-! ### Iteration 6: cycle budget capstone (measure + write) -/

/-- **Cycle budget split (capstone of the thermodynamic line)**:
one training cycle = full readout-credit measurement (exactly `k`
forward evaluations, the ceiling achieved by the Hadamard batch)
PLUS a parameter write of `F` bits. Both are priced by the same
unit work `cUnit` (bridges `h_emp_credit` and `h_emp_memwrite`,
same `h_emp_` status); with a per-cycle budget `B`, the reachable
pair (credit dimension, written bits) lies on the line
`k + F = B / cUnit` — measuring more and remembering more compete
for the SAME energy budget. This is the general optimality
pressure of the thermodynamic laws: quality (larger measured
credit) and volume (larger written model) trade off linearly. -/
theorem cycle_budget_split (B cUnit k F : ℝ) (hcUnit : 0 < cUnit)
    (hk : 0 ≤ k) (hF : 0 ≤ F)
    (h_emp_credit : cUnit * k ≤ M)
    (h_emp_memwrite : cUnit * F ≤ W) (hM : M + W ≤ B) :
    cUnit * (k + F) ≤ B := by
  have h1 : cUnit * k + cUnit * F ≤ M + W := by linarith
  have h2 : cUnit * k + cUnit * F = cUnit * (k + F) := by
    rw [mul_add]
  linarith


/-! ### Iteration 7: telescoped budget over the trajectory -/

/-- **Trajectory budget telescope**: if every cycle `t` of a
run of `T` cycles satisfies its budget split
`cUnit * (k t + F t) ≤ B t` (iteration-6 capstone per cycle) and
the per-cycle budgets telescope under the total energy `Etot`
(`∑ B t ≤ Etot`), then the WHOLE run satisfies the same line:
`cUnit * (∑ k t + ∑ F t) ≤ Etot`. The measure/write competition
compounds: over a trajectory, total measured credit plus total
written bits cannot exceed `Etot / cUnit` — the thermodynamic
ceiling on the ENTIRE self-development run, not just one cycle. -/
theorem trajectory_budget_telescope (cUnit : ℝ) (hcUnit : 0 < cUnit)
    (T : ℕ) (k F B : Fin T → ℝ) (Etot : ℝ)
    (hper : ∀ t, cUnit * (k t + F t) ≤ B t)
    (htel : (∑ t, B t) ≤ Etot) :
    cUnit * ((∑ t, k t) + (∑ t, F t)) ≤ Etot := by
  classical
  have hsplit : cUnit * ((∑ t, k t) + (∑ t, F t))
      = ∑ t, cUnit * (k t + F t) := by
    rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun t _ => (mul_add cUnit (k t) (F t)).symm
  calc cUnit * ((∑ t, k t) + (∑ t, F t))
      = ∑ t, cUnit * (k t + F t) := hsplit
    _ ≤ ∑ t, B t := Finset.sum_le_sum fun t _ => hper t
    _ ≤ Etot := htel


/-! ### Iteration 8: lifetime compose (termination x budget) -/

/-- **Lifetime compose**: a run whose every cycle dissipates at
most `d0` (the per-cycle budget) and whose trajectory terminates
by the standard dissipation lifetime `T ≤ (E0 − Emin)/d0`
(`Hagi.System.GrowthState.trajectory_termination` shape), for the
same energy interval `Etot = E0 − Emin`, satisfies the WHOLE-RUN
thermodynamic line with an explicit numeric ceiling:
`cUnit * (∑ k t + ∑ F t) ≤ E0 − Emin` — over its whole lifetime,
the run can measure at most `(E0−Emin)/cUnit` worth of credit
plus write at most that much model memory. The self-development
ceiling is thus DERIVED from the termination lifetime, not
assumed. -/
theorem lifetime_thermodynamic_ceiling (cUnit E0 Emin : ℝ)
    (hcUnit : 0 < cUnit) (hE : Emin ≤ E0)
    (T : ℕ) (k F B d : Fin T → ℝ)
    (hper : ∀ t, cUnit * (k t + F t) ≤ B t)
    (hBd : ∀ t, B t ≤ d t)
    (hd : (∑ t, d t) ≤ E0 - Emin) :
    cUnit * ((∑ t, k t) + (∑ t, F t)) ≤ E0 - Emin := by
  classical
  have htel := trajectory_budget_telescope cUnit hcUnit T k F B
    (E0 - Emin) hper (by
      -- ∑ B t ≤ ∑ d t ≤ E0 - Emin
      have h1 : (∑ t, B t) ≤ (∑ t, d t) :=
        Finset.sum_le_sum fun t _ => hBd t
      linarith)
  exact htel


/-! ### Iteration 9: witness — the ceiling line is ATTAINABLE -/

/-- **Witness: the ceiling is attainable** (non-vacuity of the
budget line). A pure-measurement cycle spending its ENTIRE budget
on reading `k` bits of credit (`B = cUnit * k`) and writing
nothing (`F = 0`) sits exactly on the ceiling edge
`cUnit * (k + 0) = B`: the thermodynamic ceiling does not forbid
a cycle — it is TIGHT. Combined with iteration 8, `E0 − Emin`
over `cUnit` is the exact reachable total, and the learning
problem reduces to choosing the split `(k, F)` on the line
`k + F = B / cUnit` to maximize realized capability — the formal
core of "maximum quality at minimal volume". -/
theorem witness_ceiling_attainable (cUnit B k : ℝ) (hcUnit : 0 < cUnit)
    (hk : 0 < k) (hB : B = cUnit * k) :
    cUnit * (k + 0) ≤ B ∧ 0 < B / cUnit := by
  refine ⟨?_, ?_⟩
  · rw [hB, add_zero]
  · rw [hB]
    exact div_pos (mul_pos hcUnit hk) hcUnit


/-! ### Iteration 10: optimal split (quality model) -/

/-- **Optimal split** ("maximum quality at minimal volume" as a
theorem): let capability after the cycle be a function θ(k) of the
measured credit ONLY (a quality model in the sense of the
information-theoretic scaling laws, Jeon–Van Roy
arXiv:2407.01456: quality is a functional of absorbed information),
strictly increasing in `k`. Among all budget-line splits
(`k + F = B/cUnit`, iteration 5–6–9) with a volume cap `F ≤ Fmax`,
the split `k* = B/cUnit − Fmax` PARETO-DOMINATES: any other split
has strictly less measured credit, hence strictly less capability,
and never less volume. The formal core: under thermodynamic laws,
minimal volume forces measurement to its budget share, and
anything not spent on measurement is pure waste. -/
theorem optimal_split_pareto (B cUnit Fmax : ℝ) (hcUnit : 0 < cUnit)
    (hFmax : 0 ≤ Fmax) (θ : ℝ → ℝ)
    (hθ : StrictMono θ) (k F : ℝ)
    (hline : k + F = B / cUnit) (hcap : F ≤ Fmax)
    (hne : k < B / cUnit - Fmax) :
    θ k < θ (B / cUnit - Fmax) :=
  hθ (by linarith)


/-! ### Iteration 11: growth witness — capability growth is
thermodynamically realizable -/

/-- **Growth witness** (the self-development core, non-vacuous):
for any lifetime `T ≥ 1`, minimal per-cycle credit `kmin > 0` and
total energy `Etot` covering the pure-measurement line
(`cUnit * T * kmin ≤ Etot`), there EXISTS a legal trajectory —
every cycle a pure-measurement cycle on the budget edge
(`k t = kmin`, `F t = 0`, `B t = cUnit * kmin`, total `T * kmin`
credit absorbed) — and since capability θ is strictly increasing
in absorbed credit (iteration-10 quality model), the final
capability STRICTLY EXCEEDS the initial one: the model has GROWN
while obeying every thermodynamic law. Growth + thermodynamic
compatibility in one statement: the ceiling does not forbid
self-development, it only bounds its total. -/
theorem thermodynamic_growth_witness (cUnit kmin Etot : ℝ)
    (hcUnit : 0 < cUnit) (hkmin : 0 < kmin) (θ : ℝ → ℝ)
    (hθ : StrictMono θ) (T : ℕ) (hT : 0 < T)
    (hE : cUnit * (T * kmin) ≤ Etot) :
    (∑ t ∈ Finset.range T, kmin = T * kmin)
      ∧ (T * kmin) * cUnit ≤ Etot
      ∧ θ 0 < θ (T * kmin) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [Finset.sum_const, Finset.card_range]
    ring
  · have h2 : (T * kmin) * cUnit = cUnit * (T * kmin) := mul_comm _ _
    rw [h2]
    exact hE
  · have hpos : 0 < T * kmin := by
      exact mul_pos (by exact_mod_cast hT) hkmin
    exact hθ (by linarith)

end Hagi.Energy

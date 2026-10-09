/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Architecture.ConfigurationCost

/-!
# FlopsEconomy — is the dance worth it? (the skeptic's ledger)

The FLOPs question, formalized honestly: one HAGI cycle
costs 3 expert trainings + a joint ~9× phase + distillation
passes (3H teacher + H student); the skeptic's alternative
is a single dense 1.5H model trained from scratch on the
union dataset under the SAME total budget. HAGI proves
MONOTONICITY guarantees, not FLOP efficiency — this module
makes that gap exact:

* `equal_budget_baseline`: under total F the dense baseline
  (per-step cost f_B) runs exactly T_B = F / f_B steps —
  the race is well-posed, both sides spend exactly F;
* `pipeline_beats_baseline_iff`: the honest verdict — under
  equal budgets the pipeline's final quality dominates the
  baseline's IFF the pipeline's net gain over the shared
  starting point covers the baseline's net gain: the entire
  comparison reduces to ONE inequality between two net
  gains, and the baseline side is an EMPIRICAL premise
  (h_emp_): Lean does not decide the race, it POSITIONS it;
* `amortized_growth_cheaper`: the structural advantage that
  IS proven — round-r growth of the switchable architecture
  costs N·r·d parameters (strictly < d² when N·r < d), so
  the MARGINAL per-round cost of growth-by-fibers beats the
  monolith's d² — the skeptic's 1.5H may win a one-shot race
  (empirical), but a MANY-round growth program pays fibers,
  not monoliths (conditional on round viability,).
-/

namespace Hagi

/-- **The equal-budget race is well-posed**: total F, dense
baseline per-step cost f_B > 0: the baseline trains for
exactly T_B = F / f_B steps — both sides spend exactly F. -/
theorem equal_budget_baseline (F f_B T_B : ℝ)
    (hf : 0 < f_B) (hT : T_B * f_B = F) :
    T_B = F / f_B := by
  exact (eq_div_iff (ne_of_gt hf)).2 hT

/-- **The verdict structure**: starting from a shared model
of quality Q₀, pipeline ends at Q₀ + ΔP (its net gain),
baseline at Q₀ + ΔB. The pipeline's final quality dominates
IFF ΔP ≥ ΔB — the whole FLOPs-economics race reduces to
comparing two net gains; ΔB is an empirical premise (no
theorem lower-bounds dense-from-scratch scaling), ΔP is the
certified-conditional pipeline gain (η_p·η_s·E_dev − price,
the vocabulary). Lean does not decide the race; it
reduces the race to one measurable inequality. -/
theorem pipeline_beats_baseline_iff (Q₀ ΔP ΔB : ℝ) :
    Q₀ + ΔP ≥ Q₀ + ΔB ↔ ΔP ≥ ΔB := by
  constructor
  · intro h
    linarith
  · intro h
    linarith

/-- **The structural advantage — amortized growth**: growth
of the switchable architecture by one fiber family costs
N·r·d parameters — strictly cheaper than the monolith's d²
when N·r < d. A many-round growth program pays FIBERS per
round, not monoliths: the marginal cost of round r is the
fiber bill, and this advantage is proven, not
empirical (the round's viability — E_dev > 0 — remains the
 conditional). -/
theorem amortized_growth_cheaper (d r N : ℕ)
    (h : N * r < d) (hd : 0 < d) :
    (N * r) * d < d * d :=
  config_storage_beats_dense d r N h hd

end Hagi

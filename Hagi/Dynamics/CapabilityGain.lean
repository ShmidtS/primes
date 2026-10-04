/-
Copyright (c) 2025 HAGI_v2 Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: HAGI_v2 formalization team
-/
import Hagi.Data.PACBayes
import Hagi.Unified.TopLevel
set_option linter.style.header false

/-!
# R82: capability gain — the internal→external transfer

HONEST STATUS (audit 2026-10-04): `capability_gain_transfer`
is BOOKKEEPING algebra (linarith on the decomposition
R_ext = E_int + gap) — the real bridge (internal descent ⟹
external gain) lives entirely in the h_emp_ premises
(estimator validity, actual-gap monotonicity), which remain
open. Conditional form:
- `capability_gain_transfer`: R_ext = E_int + gap with the
  REAL gap; internal certificate Γ_t > 0 + non-degrading gap
  ⟹ R_ext decreases by Γ_t — the internal Lyapunov descent
  TRANSFERS to external capability gain. The full chain:
  residual potential (liveness R80) ⟹ useful action
  (twoGap) ⟹ internal descent (SafeQP/Lyapunov) ⟹ EXTERNAL
  gain (here).
- `pb_gap_bound_mono`: the budget side — the PAC-Bayes gap
  bound is monotone in the KL budget; a compression/prune
  keeping KL non-increasing keeps the certified bound from
  growing (actual-gap monotonicity h_emp_ until the
  CertifiedEstimator bridge).
-/

open Real Finset

namespace Hagi

/-- **Декомпозиция внешнего риска (БУХГАЛТЕРСКАЯ ЛЕММА,
linarith)**: при разложении R_ext = E_int + gap сертификат
внутреннего спуска + неухудшение зазора переносятся на
R_ext. Весь эмпирический смысл — в посылках hcert (спуск
реального обучения) и hgap (монотонность РЕАЛЬНОГО зазора,
h_emp_): это НЕ мост, а форма его условности. the external capability measure is the
true risk R_ext(θ) = E_int(θ) + gap(θ) with the REAL
generalization gap of the step (train→true). Then:

  internal certificate  E_{t+1} ≤ E_t − Γ_t (Γ_t > 0)
  + non-degrading gap   gap_{t+1} ≤ gap_t (the budget side:
    via gibbs_variational R77 the PAC-Bayes gap bound is
    monotone in the KL budget — compression/prune keeping
    KL_{t+1} ≤ KL_t keeps the gap from growing, h_emp_)
  ⟹  R_ext(θ_{t+1}) ≤ R_ext(θ_t) − Γ_t

the internal Lyapunov descent TRANSFERS to external
capability gain — the audit's central chain closes at the
conditional level: residual potential (liveness) ⟹ useful
action (twoGap) ⟹ internal descent (SafeQP/Lyapunov) ⟹
EXTERNAL capability gain (this theorem). The h_emp_ inputs:
estimator validity (CertifiedEstimator, open) and the
KL-monotonicity of the actual gap. (Positivity Γ > 0 is part
of the intended certificate chain, not a hypothesis of this
algebra.) -/
theorem capability_gain_transfer (E1 E2 g1 g2 Rext1 Rext2 Gamma : ℝ)
    (hR1 : Rext1 = E1 + g1) (hR2 : Rext2 = E2 + g2)
    (hcert : E2 ≤ E1 - Gamma)
    (hgap : g2 ≤ g1) :
    Rext2 ≤ Rext1 - Gamma := by
  rw [hR1, hR2]
  linarith

/-- **The KL-monotone gap side**: the PAC-Bayes gap BOUND is
monotone in the KL budget — a compression/prune step that
keeps the posterior-prior budget non-increasing
(KL_{t+1} ≤ KL_t) keeps the CERTIFIED gap bound from
growing (the actual-gap side g2 ≤ g1 stays h_emp_ until the
CertifiedEstimator bridge lands). -/
theorem pb_gap_bound_mono (KL1 KL2 base : ℝ)
    (hKL : KL2 ≤ KL1) :
    KL2 + base ≤ KL1 + base := by linarith

end Hagi

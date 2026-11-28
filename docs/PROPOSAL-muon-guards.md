# PROPOSAL: Muon step guards and telemetry for the first layer W1

**Status: `PROPOSAL-index.md` (single source of truth).**

For: the HAGI_v2 implementation agent. Modules
`Hagi/Theory/{FirstLayerGrad,BatchRankOne,MuonSpectral,
MuonIsometry,NewtonSchulzSigma,MuonAlignment,MuonDescent,MuonDescentW1,
MuonWide}.lean`. Self-contained: no primes-repo context needed. All
Lean anchors are proved and frozen in primes. This document is a
proposal only: primes does not edit HAGI_v2 code (user-push).

**Changed algorithm: NO.** The update
`W1 -= (cos_lr*0.7)*newton_schulz_orthogonalize(m1, iters=3)`
stays byte-identical. The proposal adds guards and telemetry only.

## (a) Context

The orthogonalizer returns `X` unchanged when `G.norm() < 1e-12`
(hagi/core.py:1355), normalises by `G / (G.norm() + eps)`
(hagi/core.py:1353), transposes to the wide form when there are more
rows than columns (core.py:1358), runs the quadratic Newton–Schulz
iteration `X = 0.5 * (3.0 * I_m - X @ X.T) @ X` (core.py:1363)
`iters` times (`iters = 4` by default in the signature, `iters = 3`
at the call site), and the growth-block layer applies the update
(core.py:1755; layer hagi/lm.py:586, batch mean CE lm.py:688).
primes proves this step is a strict descent step for the layer; the
code never checks the premises the proof needs.

## (b) What is proved (and what it assumes)

For the first layer `W1 : ι → δ → ℝ` (code shape `dim × hidden`,
any shape since the rectangular results; square case earlier),
outside the relu kink, with the batch gradient
`G = −Σ_t g_t ⊗ x_t ≠ 0` and `Ĝ = G/‖G‖_F`:

- `muon_step_useful_w1`, `muon_step_useful_w1_batch`
  (Hagi/Theory/MuonDescentW1.lean:104/:193):
  `∃ η > 0, CE(W1 − η·wide_iter k Ĝ) < CE(W1)`.
- Any shape (Hagi/Theory/MuonDescentW1Rect.lean):
  `muon_step_useful_w1_rect'`, `muon_step_useful_w1_rect_batch'`
  (:348/:369); the square-layer pair `muon_step_useful_w1`,
  `muon_step_useful_w1_batch` sits at :134/:203.
- `muon_step_inner_ge_frob` (Hagi/Theory/MuonDescent.lean:136):
  `⟨G, ns_k(Ĝ)⟩ ≥ ‖G‖_F` — first-order drop at least that of the
  sign step (`muon_vs_sign_first_order`, :196).
- `muon_near_optimal` (Hagi/Theory/MuonAlignment.lean:131);
  `normed_sigma_le_one` (MuonDescent.lean:122):
  `⟨Ĝ, ns₃(Ĝ)⟩ ≥ (39/40)·Σ_{σ i ≥ 1/2} σ i(Ĝ)`
  (`ns_sigma_min_three`, NewtonSchulzSigma.lean:126).
- Momentum (`Hagi/Theory/MomentumAlign.lean`): the code keeps
  `m1 = 0.85·m1 + 0.15·gW1` (core.py:1754; no Nesterov term,
  no bias correction) and orthogonalises `m1`. Proved:
  `momentum_align` (:140): `⟪G,m⟫ = 0.15‖G‖² + 0.85⟪G,m_prev⟫`;
  `momentum_align_ge` (:169): if `⟪G,m_prev⟫ ≥ 0` then
  `⟪G,m⟫ ≥ 0.15‖G‖²`; `momentum_align_ge_grad` (:179): if
  `⟨G,m_prev⟫ ≥ ‖G‖²` then `⟪G,m⟫ ≥ ‖G‖²`; `momentum_align_cs` (:149):
  always `⟪G,m⟫ ≥ (1−μ)‖G‖² − |μ|·‖G‖·‖m_prev‖` (so the unconditional
  lower bound `(1−μ)‖G‖²` is false — witness `m_prev = −G/2`);
  `muon_momentum_bound` (:419): with `X = ns_k(m̂)`,
  `‖m‖_F − ‖G−m‖_F·‖X‖_F ≤ ⟨G, X⟩`; `muon_momentum_third` (:442): if
  `‖G−m‖_F·‖X‖_F ≤ ‖m‖_F/2` then `‖G‖_F/3 ≤ ⟨G, X⟩` (the step keeps at
  least a third of the first-order drop of the gradient Muon step;
  `‖X‖_F ≥ 1`, `momStep_norm_ge_one`); `dir_drop_optimal` (:112): along
  any direction `d`, `γ* = a/(L‖d‖²)`, drop `a²/(2L‖d‖²)`, `a = −⟪∇f,d⟫`.

Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound`.

Premises the code does not check: `G ≠ 0`; that `G` is what is
orthogonalised (the code orthogonalises the momentum buffer `m1`);
the step size `cos_lr·0.7` is the `η` that only exists; a descent
lemma (`L(W − ηX) ≤ L(W) − η⟨G,X⟩ + η²L/2·‖X‖²`) is not formalised.

## (c) Guards and telemetry (minimal diff, `core.py` around :1353/:1363/:1755)

- (a) **Zero gradient — skip. ALREADY IN THE CODE (core.py:1355)**
  (`if norm < 1e-12: return X`), before the division at core.py:1353
  in source order. Nothing to port; recorded so the theory premise
  `G ≠ 0` has its code-side guard. Theory: every statement needs
  `G ≠ 0`. Limit: the guard is on the norm of the buffer the
  code orthogonalises (`m1`), not of the gradient `G` of the theory.
- (b) **Normalisation warning.** After core.py:1363 (iters loop) log
  a warning if `σ_max(X_out) > 1 + 1e-6`. Theory: the iterates of the
  normalised gradient have `σ ≤ 1` (`normed_sigma_le_one`); a
  violation means the input was not Frobenius-normalised (e.g. the
  momentum buffer's scale) — the theorem does not apply.
- (c) **Operational `∃η`.** Accept the step only if
  `L(W1 − η·X₃) < L(W1)` on a small fixed batch (one extra forward
  with the candidate update; on failure halve `η`, ≤ 6 halvings, then
  skip the step). Theory: `muon_step_useful_w1_batch` gives existence
  of a descending `η`; this check finds it at runtime. This is the
  only line that changes behaviour, and only by rejecting a step that
  increased the loss.
- (d) **Telemetry per step:** `⟨G, X₃⟩ / ‖X₃‖_F` and `‖G‖₁ / √(mn)`
  (`G` the gradient, `X₃` the applied direction). Theory: the first
  is the certified first-order drop up to the factor
  `‖X₃‖_F/‖G‖_F` (`muon_step_inner_ge_frob`); the second is the
  sign-step reference of the same order. Both are diagnostics, not
  gates.

## (d) What this gives (and what it costs)

Gives: the code refuses the two states where the theorem is silent
(zero gradient, un-normalised input) and never takes a Muon step
that raises the loss on the check batch.

Costs: (c) one extra forward per Muon step (plus halvings); (b) one
SVD-free bound — use `torch.linalg.matrix_norm(X, ord=2)` on the small
matrix or skip the check when the layer is large.

## (e) Validation criterion

Log per step `inner = ⟨G, X₃⟩/‖X₃‖_F`, `frob = ‖G‖_F`, `real_drop`, and
the momentum telemetry `align = ⟨G, m1⟩/‖G‖²` (witnessed by
`momentum_align`: `align = 0.15 + 0.85·⟨G,m1_prev⟩/‖G‖²`),
`resid = ‖G−m1‖_F·‖X₃‖_F/‖m1‖_F` and `frob_m = ‖m1‖_F`. Accept the port
iff on a full run: `real_drop > 0` on every accepted step; skipped steps
are counted and reported (no target). Momentum criterion
(`muon_momentum_third`): whenever `resid ≤ 1/2` (and guard (b) did not
fire), `inner ≥ ‖G‖_F/3`; whenever `align ≥ 1`, `inner` is compared
against `‖m1‖_F`, not `‖G‖_F`. `inner ≥ frob − 1e-5` is no longer the
right reference: the direction is `ns₃(m1)`, the proved bound is
`inner ≥ ‖m1‖_F − resid·‖m1‖_F`, which can be below `‖G‖_F`.

## (f) Limits

- (1) The descent theorems first covered the square layer only. The
  rectangular Newton–Schulz iterate is formalised in
  `Hagi/Theory/MuonWide.lean`: the code line core.py:1363 equals the
  proved step; the iterates keep the singular bases; the optimum
  over row isometries `ΔΔᵀ = I` is `Σ σ i`. The real wide SVD is a
  theorem (`exists_wide_svd`, `Hagi/Theory/WideSVD.lean`), so T1',
  T2 and the optimum hold unconditionally, as do T3 and a descent
  certificate for a wide `G ≠ 0` (`wnormed_sigma_le_one`,
  `wide_alignment_ge_gradient'`, `muon_step_useful_wide`,
  Hagi/Theory/WideSVD.lean; the tall buffer is the same
  `wide_iter k G` by `ns_step_transpose`, Hagi/Theory/MuonWide.lean).
  The bridge from the layer (`dim × hidden`, `card ι ≤ card δ`) to
  the wide carrier is Hagi/Theory/MuonDescentW1Rect.lean; the
  dimension premise is removed (`tall_alignment_ge_gradient`,
  `alignment_ge_gradient_any`, `muon_step_useful_w1_rect'`): a
  layer of any shape is covered.
- (2) The code orthogonalises `m1`, not `G`. The momentum is inside
  the theory up to the residual `G − m1` (`muon_momentum_bound`,
  `muon_momentum_third`); what stays outside: the value `0.85` is not
  derived, the code does not log `⟪G,m1⟫` and `‖G−m1‖_F`, and the
  certificate is conditional on the residual being small (telemetry (e)).
- (3) `cos_lr·0.7` is not the proved `η`; guard (c) is a runtime
  substitute, not a theorem.
- (4) Check batch ≠ full distribution: acceptance on one batch says
  nothing about other batches or holdout.
- (5) Float soundness: the theory is exact arithmetic; the code is
  float32. The validation loop (e) is the runtime check.
- (6) Anchors are frozen in primes; re-verify before port.

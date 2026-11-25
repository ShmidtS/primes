# PROPOSAL: Muon step guards and telemetry for the first layer W1

**Status: theory implemented in primes (C668–C676, C678); code-side pending in HAGI_v2 (guard (a) is already in the code).**

For: the HAGI_v2 implementation agent. Written by the primes agent
(C677; modules `Hagi/Theory/{FirstLayerGrad,BatchRankOne,MuonSpectral,
MuonIsometry,NewtonSchulzSigma,MuonAlignment,MuonDescent,MuonDescentW1,
MuonWide}.lean`).
Self-contained: no primes-repo context needed. All Lean anchors are
proved and frozen in primes (freeze identity 9163 after C678). This document is a
proposal only: primes does not edit HAGI_v2 code (user-push).

**Changed algorithm: NO.** The update
`W1 -= (cos_lr*0.7)*newton_schulz_orthogonalize(m1, iters=3)`
stays byte-identical. The proposal adds guards and telemetry only.

## (a) Context (one line)

Read-only @ca52eb4: the orthogonalizer returns `X` unchanged when
`G.norm() < 1e-12` (hagi/core.py:1355), normalises by
`G / (G.norm() + eps)` (hagi/core.py:1353), transposes to the wide form
when there are more rows than columns (core.py:1358), runs the quadratic
Newton–Schulz iteration `X = 0.5 * (3.0 * I_m - X @ X.T) @ X`
(core.py:1363) `iters` times (`iters = 4` by default in the signature,
`iters = 3` at the call site), and the growth-block layer applies the
update (core.py:1755; layer hagi/lm.py:586, batch mean CE lm.py:688).
primes proves this step is a strict descent step for the layer; the
code never checks the premises the proof needs.

## (b) What is proved (and what it assumes)

For the square first layer `W1 : n → n → ℝ`, outside the relu kink,
with the batch gradient `G = −Σ_t g_t ⊗ x_t ≠ 0` and `Ĝ = G/‖G‖_F`:

- `muon_step_useful_w1`, `muon_step_useful_w1_batch`
  (Hagi/Theory/MuonDescentW1.lean:104/:193):
  `∃ η > 0, CE(W1 − η·ns_k(Ĝ)) < CE(W1)`.
- `muon_step_inner_ge_frob` (Hagi/Theory/MuonDescent.lean:136):
  `⟨G, ns_k(Ĝ)⟩ ≥ ‖G‖_F` — first-order drop at least that of the
  sign step (`muon_vs_sign_first_order`, :196).
- `muon_near_optimal` (Hagi/Theory/MuonAlignment.lean:131) with
  `normed_sigma_le_one` (MuonDescent.lean:122):
  `⟨Ĝ, ns₃(Ĝ)⟩ ≥ (39/40)·Σ_{σ i ≥ 1/2} σ i(Ĝ)`
  (`ns_sigma_min_three`, NewtonSchulzSigma.lean:126).

Axioms of every theorem: `propext`, `Classical.choice`, `Quot.sound`.

Premises the code does not check: `G ≠ 0`; `G` is what is
orthogonalised (the code orthogonalises the momentum buffer `m1`);
the layer is square (the code's `W1` is `dim × hidden`); the step
size `cos_lr·0.7` is the `η` that only exists; a descent lemma
(`L(W − ηX) ≤ L(W) − η⟨G,X⟩ + η²L/2·‖X‖²`) is not formalised.

## (c) Guards and telemetry (minimal diff, `core.py` around :1353/:1363/:1755)

- (a) **Zero gradient — skip. ALREADY IN THE CODE @ca52eb4:1355**
  (`if norm < 1e-12: return X`), before the division at core.py:1353
  in source order. Nothing to port; recorded so the theory premise
  `G ≠ 0` has its code-side guard. Theory: every statement needs
  `G ≠ 0`. Honest limit: the guard is on the norm of the buffer the
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

## (e) Validation criterion (loop-5 style)

Log per step `inner = ⟨G, X₃⟩/‖X₃‖_F`, `frob = ‖G‖_F`, `real_drop`.
Accept the port iff on a full run: `inner ≥ frob − 1e-5` whenever
guard (b) did not fire; `real_drop > 0` on every accepted step;
skipped steps are counted and reported (no target).

## (f) Honest limits

- (1) Square layer only in the descent theorems; `dim × hidden` in
  the code. The rectangular Newton–Schulz iterate is formalised in
  primes (C678, `Hagi/Theory/MuonWide.lean`: the code line
  core.py:1363 equals the proved step; the iterates keep the singular
  bases; the optimum over row isometries `ΔΔᵀ = I` is `Σ σ i`) — but
  under the hypothesis that `G` has a real wide SVD, which is not
  proved, and the descent certificate of C676 is not yet instantiated
  on that carrier.
- (2) The code orthogonalises `m1`, not `G`; momentum is outside the
  theory.
- (3) `cos_lr·0.7` is not the proved `η`; guard (c) is a runtime
  substitute, not a theorem.
- (4) Check batch ≠ full distribution: acceptance on one batch says
  nothing about other batches or holdout.
- (5) Float soundness: the theory is exact arithmetic; the code is
  float32. The validation loop (e) is the runtime check.
- (6) Anchors are frozen in primes; re-verify before port.

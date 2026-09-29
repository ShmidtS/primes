/-
Copyright (c) 2026 HAGI_v2 authors. All rights reserved.
-/
import Hagi.Hadamard
import Hagi.Kronecker
import Hagi.DFT3
import Hagi.BlockDiag
import Hagi.Merge
import Hagi.Ternary
import Hagi.ErrorProp
import Hagi.Attention
import Hagi.Lift
import Hagi.Concat
import Hagi.Ridge
import Hagi.Select
import Hagi.Mix
import Hagi.KVWater
import Hagi.Ambig
import Hagi.Grow
import Hagi.GapLaw
import Hagi.RealF3
import Hagi.Element
import Hagi.Joint
import Hagi.GenCycle
import Hagi.Compound
import Hagi.RankBudget
import Hagi.NCE
import Hagi.NCEVar
import Hagi.DField
import Hagi.ValueOfRead
import Hagi.NCEExact
import Hagi.LazyAdam
import Hagi.ComputeBudget
import Hagi.DFieldKKT
import Hagi.DBridge
import Hagi.Distill
import Hagi.SafeQP
import Hagi.Dominate
import Hagi.Decompose
import Hagi.FreeEnergy
import Hagi.GrowthGate
import Hagi.MergeIdentity
import Hagi.BranchScale
import Hagi.TernaryLean
import Hagi.MergeScaling
import Hagi.F3Root
import Hagi.SinkCost

set_option linter.style.header false

/-!
# Formalization of HAGI_v2

This library formalizes the mathematical core of the HAGI_v2 project
(E:/HAGI_v2) — a "ternary RD-channel causal language model" grown from
small domain experts instead of being trained from scratch.

The modules correspond to the mathematical constructions of the project:

* `Hagi.Hadamard` — the Sylvester (Walsh) Hadamard matrices `H_n / √n`
  used by the Hadamard cross-expert mixer (`src/hagi/model/merge.py`,
  GROWING_HYPOTHESIS.md, Part V). Orthonormality: `H * Hᵀ = n • 1`.
* `Hagi.Kronecker` — the Kronecker product `⊗ₖ` preserves
  (conjugate-)orthonormality; underlies the recursive/local Hadamard
  mixer `Q = H_{g_k} ⊗ ⋯ ⊗ H_{g_1}` (GROWING_HYPOTHESIS.md, Part VI)
  and the DFT-3 Kronecker recursion `F₃ᵏ`.
* `Hagi.DFT3` — the ternary DFT-3 (F₃) mixer of the recursive ternary
  growth cycle (README.md "Growth cycle algorithm"): `F₃` is unitary,
  every entry has modulus `1/√3`, and the Kronecker powers `F₃ᵏ` are
  unitary — "uniform mixing with no blind channels".
* `Hagi.BlockDiag` — block-diagonal merge: at step 0 the merged model
  computes *exactly* the N independent experts
  (GROWING_HYPOTHESIS.md "Механизм", `src/hagi/model/merge.py`).
* `Hagi.Merge` — step-0 equivalence of the mixer merge: with the head
  pre-rotation `W' = W * Qᵀ`, the mixer path `W' *ᵥ (Q *ᵥ x) = W *ᵥ x`;
  the concat head sums the experts' logits (the `logit_scale / √N`
  observation); an orthonormal mixer preserves the inner product —
  it is information-neutral.
* `Hagi.Ternary` — ternary quantization (`dsv4_experts.py`,
  `dsv4_refit_experts.py`): 5 trits pack injectively into a byte
  (`3⁵ = 243 ≤ 256`), and nearest-grid rounding on the ternary
  `{-1, 0, +1}` / int4 `±7` grids has error at most half a step.
* `Hagi.ErrorProp` — the telescopic error-accumulation law of the
  sequential compression pass: `δ_{l+1} = J_l δ_l + r_l` with
  Lipschitz `‖J_l‖ ≤ α` gives `‖δ_L‖ ≤ α^L ‖δ₀‖ + ρ Σ αⁱ`; for the
  measured `α ≤ 1` this is the Σ-accumulation of expected error
  (README.md "telescopic fitting").
* `Hagi.Attention` — softmax-weighted error damping: an error `eᵢ`
  entering the attention output weighted by `pᵢ` contributes at most
  `max ‖eᵢ‖` — the principle behind the KV precision pyramid
  (README.md "Target KV design").

* `Hagi.Lift` — the parent-preserving ternary lift `Q(π/2)` of the
  recursive F3 tree (`ParentPreservingTernaryLift`, commit series
  2026-09-27): orthogonal, fixes the diagonal `(1,1,1)` pointwise —
  "lifting three identical parent copies is the identity on their
  diagonal", the property that makes tree depth meaningful; the leaf
  subspace is invariant; the root-mode cortex preserves leaf
  equality (ARCHITECTURE_V2).
* `Hagi.Concat` — the concat==child invariant and the temperature
  correction (commit `74e7d30`, `test_merge_invariants.py`): the
  concat head of N identical children sums the block contributions
  (`n • (W *ᵥ x)`), the identity scale is forced to be `1/n` (the
  `logit_scale = child/n` fix), and rescaled logits reproduce the
  softmax only on constant logits — a CE change from a temperature
  rescale is an artifact, not a quality gain.

Empirical measurements (RMS errors, benchmark scores, saturation
curves) are not mathematical statements and are intentionally out of
scope.
-/

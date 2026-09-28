# primes

Lean 4 / Mathlib formalization projects.

## HAGI_v2 formalization (`Hagi/`)

The `Hagi` library formalizes the mathematical core of the
HAGI_v2 project — the ternary RD-channel causal language model grown
from small domain experts (E:/HAGI_v2). Empirical measurements
(benchmark scores, RMS errors, saturation curves) are not mathematical
statements and are out of scope.

| Module | Formalizes (HAGI_v2 source) |
| --- | --- |
| `Hagi.Hadamard` | Sylvester/Walsh Hadamard matrices of the cross-expert mixer (`src/hagi/model/merge.py`, GROWING_HYPOTHESIS.md Part V): `H * Hᵀ = 2^k • 1`, so `H/√2^k` is orthonormal; every entry ±1 — uniform mixing, no blind channels. |
| `Hagi.Kronecker` | Kronecker products preserve (conjugate-)orthonormality — the algebra behind the recursive/local Hadamard mixer `Q = H_{g_k} ⊗ ⋯ ⊗ H_{g_1}` (Part VI) and the DFT-3 Kronecker recursion. |
| `Hagi.DFT3` | The ternary DFT-3 (F₃) mixer of the recursive growth cycle (README "Growth cycle algorithm"): `ω = e^{2πi/3}`, the character `χ₃`, orthogonality of nontrivial characters on `(ZMod 3)^k`; the k-fold mixer `F₃ᵏ` is unitary with all entries of modulus `1/√(3^k)`. |
| `Hagi.BlockDiag` | Block-diagonal merge (`GROWING_HYPOTHESIS.md "Механизм"`): at step 0 the merged linear layer `diag(W₁,…,W_N)` computes exactly the N independent experts. |
| `Hagi.Merge` | Step-0 equivalence of the Hadamard mixer merge: head pre-rotation `W' = W Qᵀ` gives `W' *ᵥ (Q *ᵥ x) = W *ᵥ x`; the concat head sums the experts' logits; orthonormal mixers preserve the dot product — information-neutral. **Two scales, do not mix**: `√n` = mixer orthonormality scale, `1/n` = logit_scale identity (the temperature-correction fix `74e7d30`). |
| `Hagi.Ternary` | Ternary quantization (`scripts/dsv4_experts.py`): 5 trits pack injectively into a byte (`3⁵ = 243 ≤ 256`); nearest-grid rounding on the ternary `{-1,0,+1}` and int4 `±7` grids has error ≤ half a step; the LS grid scale `∑qx/∑q²` is squared-error-optimal at a fixed pattern (normal equations) — the closed form behind “LS scales instead of amax”. |
| `Hagi.ErrorProp` | Telescopic error accumulation of the sequential compression pass (README "telescopic fitting"): `δ_{l+1} = J_l δ_l + r_l` with `‖J_l‖ ≤ α` gives `‖δ_L‖ ≤ α^L‖δ₀‖ + ρ Σ αⁱ`; for the measured `α ≤ 1` this is the Σ-accumulation of expected error. The second-moment version: under residual orthogonality, `‖δ_L‖² ≤ α^(2L)‖δ₀‖² + Σ w_l ρ_l²` with `w_l = Π_{k>l} α_k²` — the layer-weighted “waterfilling” objective for bit allocation. |
| `Hagi.Lift` | The parent-preserving ternary lift `Q(π/2)` of the recursive F3 tree (`ParentPreservingTernaryLift`, merge.py): orthogonal, fixes the diagonal `(1,1,1)` pointwise — lifting three identical parent copies is the identity, the property that makes tree depth meaningful; the leaf subspace (sibling differences) is invariant; the root-mode cortex (writing one value to all leaves) preserves leaf equality — the identity invariant survives the cortex at init. |
| `Hagi.Ridge` | The W2 re-solve of the terni4 recipe (`dsv4_refit_experts.py`, `ridge_solve_guarded`): the ridge objective `‖Xw−y‖²+λ‖w‖²` and **`ridge_optimal`** — any solution of the normal equations `Xᵀ(Xw−y)+λw=0` is a global minimizer (complete-the-square; the pinv guard is about existence, not optimality). This is why the pre-quantization re-solve is safe: it provably extracts everything the quantized upstream can explain, leaving only fresh residual for the telescopic error budget. |
| `Hagi.Concat` | The concat==child invariant and the temperature correction (commit `74e7d30`, `test_merge_invariants.py`): the concat head of N identical children sums the block contributions (`n • (W*ᵥx)`); the identity scale is forced to be `1/n` (the `logit_scale = child/n` fix — the old `/√N` provably breaks the invariant); rescaled logits (`c ≠ 1`) reproduce the softmax only on constant logits. **Ensemble theorem**: `CE(mean logits) ≤ mean CE` (Cauchy/Jensen for lse, two children; 2^k by iteration) — merged-at-1/2 beats the average child, and CAN beat every child (complementary experts), so "concat cannot beat the best leaf" is false in general. |
| `Hagi.Attention` | Softmax-weighted error damping — the principle of the KV precision pyramid (README "Target KV design"): an error entering the attention output weighted by `pᵢ` contributes at most `max‖eᵢ‖`. |

Build: `lake build` (toolchain `leanprover/lean4:v4.32.0-rc1`, Mathlib
cache included). Every theorem is fully proved — no `sorry`.

## GitHub configuration

To set up your new GitHub repository, follow these steps:

* Under your repository name, click **Settings**.
* In the **Actions** section of the sidebar, click "General".
* Check the box **Allow GitHub Actions to create and approve pull requests**.
* Click the **Pages** section of the settings sidebar.
* In the **Source** dropdown menu, select "GitHub Actions".

After following the steps above, you can remove this section from the README file.

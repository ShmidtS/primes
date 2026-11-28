# PROPOSAL 38 — Thresholds as formulas: replace three constants that sit below the radius

**Status:** `PROPOSAL-index.md` (single source of truth).

One rule (`Hagi/Unified/DecisionRule.lean`): act iff `ĝ − radius(n, α) > λ·ΔB`.
Three current constants contradict it; each has an exact replacement
(`docs/DERIVED-CONFIG.md` §3). σ² = 1.6 is the code's own window-CE variance.

| constant | code | problem | replacement |
|---|---|---|---|
| `ANCHOR_SE_MULT` / `ANCHOR_MIN_WINDOWS` | 4.0 / 32 | 4·SE is not a finite-sample guarantee; radius at 32 windows is 1.5–3.0 nat vs tol 0.25 | gate on `radius(σ², b, n, α)`; `ANCHOR_MIN_WINDOWS = n*(0.25) = ⌈1/rootT²⌉` = 463 (Bonf 1) … 978 (Bonf 16) |
| `ADAPTER_MIN_GAIN` with `ADAPTER_VAL_WINDOWS = 4096` | 0.005 | radius(4096) = 0.073 ≫ 0.005: gains indistinguishable from noise pass | either `n = n*(0.005) = 764 311` windows, or `MIN_GAIN = radius(n)` (0.073 at 4096) — the gate already uses `paired_margin_eb`, so only the floor must move |
| `choose_emb_rows2(lam)` | 5e-4 | λ is the MDL byte price `8·ln 2 / N`; 5e-4 corresponds to N ≈ 11 kB, the live book is ≈ 400 kB → λ overestimated ≈ 36×, too few rows chosen | `lam = 8 * math.log(2) / len(data)` |

## Patch

```python
# unified.py
ANCHOR_MIN_WINDOWS = "auto"     # n*(tol) from the measured window variance
def _anchor_windows_min(self, tol, alpha=0.05, bonf=WORST_GATE_BONF):
    sig2 = self._window_ce_variance(); A = math.sqrt(2 * sig2 * math.log(2 * bonf / alpha)); B = 2 * self.CE_RANGE * math.log(2 * bonf / alpha)
    return math.ceil(1 / ((-A + math.sqrt(A * A + 4 * B * tol)) / (2 * B)) ** 2)   # ⌈1/rootT²⌉
ADAPTER_MIN_GAIN = "radius"     # floor = paired_margin_eb(d, n_states, delta) already computed by the gate
# optimal_lm.py / unified.choose_emb_rows2
lam = 8 * math.log(2) / max(1, sum(len(self._domain_bytes(n, d)) for n, d in self.domains.items()))
```

Trajectory-neutral until enabled; each change *tightens* a gate or moves the
sweep toward more stage-two rows at the same certificate.

## Test

```python
def test_anchor_windows_match_rootT():
    assert U.Unified._anchor_windows_min(m, 0.25) == 463   # σ² = 1.6, b = 3, Bonf 1
def test_mdl_lambda_inverse_data():
    assert abs(U.lam_mdl(400_000) - 1.386e-5) < 1e-8
```

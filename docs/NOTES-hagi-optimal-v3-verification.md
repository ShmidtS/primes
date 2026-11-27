# Verification note: HagiOptimalV3 report (cycle 101)

Source: user report (4-domain continual benchmark `code/json/text/algo_kv`,
prototype `/var/hagi_prime/`, not on this machine). All nine cited theory nodes
exist in primes (AdaptiveChunking, HNet2, CortexFiber, OrthoInjection,
DepthExitCert, EF21Scale, AdamSNR, JointCost, MirrorHedge) — Chesterton check
passed before adding anything.

## Numbers recomputed from formulas

| Claim | Recomputed | Verdict |
|---|---|---|
| L2 fire 19.9 % vs r=2 (50 %) → 2.5× | 2.51× | ✓ |
| 19.9 % vs full layer → 5× | 5.03× | ✓ |
| mean CE row 1 | 0.8732 | ✓ |
| mean CE rows 2/3/4/5 | 0.8493 / 0.8485 / 1.7418 / 1.0057 | report says 0.8489 / 0.8482 / 1.7416 / 1.0059 — 3rd–4th digit mismatch (rounding of inputs?) |
| worst forgetting 0.2674 → 0.0576 = 4.4× | 4.64× | report understates |
| AdamSNR memory −31.4 % | 7680/24492 = 0.3136 | ✓ |
| "saving 7.7k floats = v_v on emb + E_bi" | 256·24 + 256·8 = 8192 ≠ 7680 | composition does not add up (7680 = 5·1536) |
| EF21 ΔCE | +0.0171 | ✓ |
| Early-exit ΔCE | −0.0077 | ✓ |
| Top-1 agreement 99.01/99.07 %, coverage 52.5/52.9/61.5 % | empirical | not reproducible here |

## What is *not* certified in the patch

`forward_with_early_exit` exits on `bypass_hit | margin > 2.0`. `margin` is a
logit gap, not a certificate: `DepthExitCert.early_exit_certificate` needs a
per-block residual bound `bres₂` and head Lipschitz `L_h`, giving
`‖Δlogits‖ ≤ L_h·bres₂`; the exit is safe iff `2·L_h·bres₂ < margin`.
`margin_exit_unbounded_without_bound` (this cycle) makes the gap explicit:
without `bres₂` no margin threshold bounds the error. The 99.07 % agreement is a
measurement, so the report's "certified early exit" is a heuristic until
`L_h·bres₂` is logged and the threshold is `2·L_h·bres₂`.

`AdaptiveHNet2Layer` training path computes `u2_all` for all positions (dense
`W_l2`); the 2.5× saving is inference-only unless the training loop also gates.

## Consequence for the code side

- PROPOSAL 31 (new): log `L_h·bres₂` per block at export and replace the fixed
  `2.0` by `2·L_h·bres₂`; keep `margin > 2.0` only as a fallback with the
  measured agreement in the ledger.
- The AdamSNR memory accounting (7680 vs 8192) must be reconciled before the
  "−31.4 %" figure is used as an anchor.

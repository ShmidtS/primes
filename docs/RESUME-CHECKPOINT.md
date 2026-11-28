# Resume checkpoint

Map, not source of truth: git is. Theory map — `docs/UNIFIED-THEORY.md`;
module index — `STATUS.md`; proposal statuses — `docs/PROPOSAL-index.md`.

## Where

- `C:\primes`: Lean 4.36 / Mathlib. CI = `bash scripts/ci.sh` with
  `export PATH="/c/Users/shmid/lean-toolchains/lean-4.36.0-windows/bin:$PATH"`
  (without it lake fails on Batteries — false BUILD FAIL).
- `C:\HAGI_v2` (reference implementation): READ-ONLY, another agent.
  Head at last check `ef61bbb`.

## State

- Every commit passes the full battery; Freeze 9663 declarations.
- Live in code: 13, 17, 26, 29 (sweep `choose_emb_rows2`, ef61bbb), 29c (Fisher row score a1a3c53/1984f43 — measured on the live book −0.55 nat at 32 rows vs my toy −0.26: theory predicted, code confirmed), anchor gate (1d14568), 34, 35 (`4f5dc81` certified worst gate), GPM default
  on (`3c19a8c`). Unwired: 25 (`gauge_balance` never called → 25b).
  Reverted without cause: 18, 30. Ready with tests: 29 (−1.0 of 2.3 nat for
  +13 % bytes), 31, 25b. No test yet: 19–21, 23, 24, 25-MLA.
- Measured on the real code (`scripts/ab_export_quant.py`, `ab_grow_init.py`):
  25b and 27 are exact identities with no CE effect at this scale — insurance,
  not gains. Keep the docstrings saying so.

## Rules learned (failures behind them in git)

- A numeric constant in a proposal is a claim: simulate against the real
  function before submitting (cap 4 → bias 1/q; α/138 → 2.09 nat radius).
- The CE-vs-k curve is not concave in k (marginal price 1.3e-3 → 3.5e-4 → 4.9e-4, ef61bbb): `kstar_minimal` needs ΔJ ∝ monotone c; on real CE use a sweep (`sweep_ge_argmin`).
- "Accepted" ≠ "wired": check `rg "<name>\(" hagi | grep -v def` before writing
  ACCEPTED.
- On a revert: log a re-approval condition; do not resubmit blind.
- DocLint R4: no backticked non-Lean names in docstrings; R5: every number is a
  file literal or marked «измерено». Docstrings must not contain `-/`.

## Continue

1. New HAGI_v2 commit → read diff, find the Lean model, probe in `.tmp/`,
   add to the sibling module, CI, commit, check the call site.
2. No new commit → no micro-theorems (YAGNI). Open with content: derive the
   guarantee class itself (floor, riskLim, δ-curve) so "ideal" becomes a
   theorem about the class, not only about the shipped program.

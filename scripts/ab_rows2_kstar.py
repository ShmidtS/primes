"""Marginal rule for the number of stage-two emb rows (ResidualVQ.kstar_minimal).

Prediction of the theorem: for residuals sorted by contribution c_k and byte
price lam (nat per byte), k* = first k with (1 - 1/rho) * c_k <= lam * b_row,
where b_row = bytes per stage-two row. This script measures c_k, rho, lam on the
real model and compares the predicted k* with the empirical minimiser of
CE + lam * bytes.  Run from HAGI_v2's root (read-only use of its code):
    python C:/primes/scripts/ab_rows2_kstar.py --steps 60
"""
import argparse, sys
import numpy as np, torch as t
sys.path.insert(0, ".")
sys.path.insert(0, "C:/primes/scripts")
from ab_export_quant import export_ce, ce, snapshot, restore, COLS_ONLY  # noqa
import ab_export_quant as AQ
from hagi.models.optimal_lm import HagiOptimalLM, HybridMuonAdamW, quant_per_row, dequant_per_row

ap = argparse.ArgumentParser(); ap.add_argument("--steps", type=int, default=60); a = ap.parse_args()
t.manual_seed(0); rng = np.random.default_rng(0)
m = HagiOptimalLM()
tmpl = rng.integers(0, 256, 32); data = np.tile(tmpl, 128)
for _ in range(200): data[rng.integers(0, len(data))] = rng.integers(0, 256)
opt = HybridMuonAdamW(*m.matrix_and_vec_params(), lr_muon=0.0, lr_adam=3e-3, momentum=0.0, wd=1e-4); opt.names = m.param_names()
for s in range(a.steps):
    x = t.as_tensor(np.stack([data[i:i + 32] for i in range(0, 2048, 32)])).long()
    y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(0, 2048, 32)])).long().to(m.device)
    opt.zero_grad(); t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)).backward(); opt.step()
x = t.as_tensor(np.stack([data[i:i + 32] for i in range(3000, 4000, 32)])).long().to(m.device)
y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(3000, 4000, 32)])).long().to(m.device)

# --- c_k: residual contribution per emb row after stage one (sorted desc) ---
W = m.emb.detach().cpu().numpy().astype(np.float64)
par, Q = quant_per_row(W, bits=2, use_had=True, rotate_rows=False)
R = W - dequant_per_row(par, Q); c = np.sort((R ** 2).sum(1))[::-1]
# --- rho: how much stage two shrinks the contribution, per selected row ---
par2, Q2 = quant_per_row(R[:128], bits=2, use_had=True, rotate_rows=False)
R2 = R[:128] - dequant_per_row(par2, Q2); rho = (R[:128] ** 2).sum(1) / np.maximum((R2 ** 2).sum(1), 1e-300)
b_row = Q2.shape[1] // 4 + par2["scales"].nbytes / Q2.shape[0]
print(f"c_0 {c[0]:.4f} c_64 {c[64]:.4f} c_128 {c[128]:.4f} c_255 {c[255]:.4f} | rows {len(c)}")
print(f"rho median {np.median(rho):.1f} (min {rho.min():.2f}, max {rho.max():.1f}) | bytes/row {b_row:.1f}")

# --- the real code path (commit 1b55ac4): OM.EMB_ROWS2 -> quantize_model/dequantize_into ---
import hagi.models.optimal_lm as OM
ks = [0, 16, 32, 64, 96, 128, 192, 256]; res = {}
emb0 = m.emb.detach().clone()
for k in ks:
    OM.EMB_ROWS2 = k; q, nb = OM.quantize_model(m, bits=2, use_had=True); OM.dequantize_into(m, q)
    res[k] = (ce(m, x, y), nb); m.emb.data.copy_(emb0)
OM.EMB_ROWS2 = 0
for k in ks: print(f"  k {k:4d}: CE {res[k][0]:.4f} bytes {res[k][1]} (+{res[k][1] - res[0][1]})")
for lam in (1e-4, 3e-4, 1e-3, 3e-3):
    tot = {k: ce_ + lam * b for k, (ce_, b) in res.items()}; k_emp = min(tot, key=tot.get)
    rho_m = float(np.median(rho)); thr = lam * b_row; marg = (1 - 1 / rho_m) * c
    pred = int(np.argmax(marg <= thr)) if (marg <= thr).any() else len(c)
    print(f"lam {lam:.0e}: empirical argmin k = {k_emp}; rule k* = {pred}; J(emp) {tot[k_emp]:.4f} J(rule, clipped) {tot[min(pred, 256) if min(pred, 256) in tot else 256]:.4f}")

# --- why the rule misses: CE gain per row vs residual contribution c vs token-frequency-weighted c ---
from collections import Counter
cnt = Counter(data[:3000].tolist()); f = np.array([cnt.get(i, 0) for i in range(len(c))], float); f = f / max(f.sum(), 1)
order = np.argsort(-c)
dCE = np.array([res[ks[i]][0] - res[ks[i + 1]][0] for i in range(len(ks) - 1)])      # CE gain per block
mc = np.array([c[order[ks[i]:ks[i + 1]]].sum() for i in range(len(ks) - 1)])            # summed c per block
mf = np.array([(f[order[ks[i]:ks[i + 1]]] * c[order[ks[i]:ks[i + 1]]]).sum() for i in range(len(ks) - 1)])  # freq-weighted
def corr(a, b): return float(np.corrcoef(a, b)[0, 1])
print(f"corr(dCE, sum c) = {corr(dCE, mc):.3f} | corr(dCE, sum f*c) = {corr(dCE, mf):.3f}")
print("per-block dCE   ", np.round(dCE, 4)); print("per-block sum c ", np.round(mc / mc[0], 3)); print("per-block f*c   ", np.round(mf / mf[0], 3))

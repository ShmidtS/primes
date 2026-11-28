"""PROPOSAL 29d probe: Fisher-scored stage-two row selection for every matrix.

Hagi/Probability/FisherRowScore.lean: the CE price of a quantisation error row e
is mean (e·x)^2 over the batch of its inputs, not |e|^2. HAGI_v2 already records
the input of every matrix (forward_seq(..., capture) stores capture[id(W)]).
This measures, per matrix, CE at equal k when rows are ranked by |res|^2 (code)
vs by rowFisherScore(X, res).  Run from HAGI_v2's root:
    PYTHONIOENCODING=utf-8 HAGI_OLD_GATE=0 python C:/primes/scripts/ab_fisher_rows.py --steps 60 --k 32
"""
import argparse, sys
import numpy as np, torch as t
sys.path.insert(0, ".")
import hagi.models.optimal_lm as OM
from hagi.models.optimal_lm import HagiOptimalLM, HybridMuonAdamW, quant_per_row, dequant_per_row

ap = argparse.ArgumentParser(); ap.add_argument("--steps", type=int, default=60); ap.add_argument("--k", type=int, default=32); a = ap.parse_args()
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
def ce(): return float(t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)))

# inputs of every matrix on a training batch
xb = t.as_tensor(np.stack([data[i:i + 32] for i in range(0, 2048, 32)])).long().to(m.device)
cap = {}
with t.no_grad(): m.forward_seq(xb, capture=cap)
mats = {n: p for n, p in m.__dict__.items() if isinstance(p, t.nn.Parameter) and p.ndim == 2 and id(p) in cap}
print("matrices with captured input:", {n: tuple(p.shape) for n, p in mats.items()})

OM.EMB_ROWS2 = "0"; q0, nb0 = OM.quantize_model(m, bits=2, use_had=True)
snap = {n: p.detach().clone() for n, p in m.__dict__.items() if isinstance(p, t.nn.Parameter)}
def restore(): 
    for n, v in snap.items(): getattr(m, n).data.copy_(v)
def run(score):
    q, nb = OM.quantize_model(m, bits=2, use_had=True); extra = 0
    for n, p in mats.items():
        par = q[n]; W = p.detach().cpu().numpy().astype(np.float64); R = W - dequant_per_row(par, par["Q"])
        X = cap[id(p)].detach().cpu().numpy().astype(np.float64)  # (B*T, in)
        if X.shape[1] != W.shape[1]: continue
        s_ = ((R @ X.T) ** 2).mean(1) if score == "fisher" else (R ** 2).sum(1)
        idx = np.argsort(-s_)[:min(a.k, len(s_))]
        par2, Q2 = quant_per_row(R[idx], bits=2, use_had=True, rotate_rows=False)
        deq = dequant_per_row(par, par["Q"]); deq[idx] += dequant_per_row(par2, Q2)
        getattr(m, n).data.copy_(t.as_tensor(deq, dtype=p.dtype).to(p.device)); extra += Q2.size // 4 + par2["scales"].nbytes
    c = ce(); restore(); return c, nb + extra
c_norm, b_norm = run("norm"); c_fish, b_fish = run("fisher")
print(f"k {a.k}: CE |res|^2 {c_norm:.4f} ({b_norm} B) | Fisher {c_fish:.4f} ({b_fish} B) | gain {c_norm - c_fish:+.4f} nat at equal bytes")

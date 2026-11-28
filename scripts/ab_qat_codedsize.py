"""PROPOSAL 37 probe: QAT with a coded-size term (cmix-neif-2.0 4.3; CodedSizeQAT.lean).

Penalty = lam * sum over matrix rows of H(hist of levels of w_row / scale_row), with soft
bins (softmax of -|w/scale - level|/tau) so it is differentiable; added on the last
`cool` steps (cool-down). Reports held-out CE and coded bytes (entropy of hard level
histograms, 2-bit) with and without the term.  Run from HAGI_v2's root:
    PYTHONIOENCODING=utf-8 HAGI_OLD_GATE=0 python C:/primes/scripts/ab_qat_codedsize.py --steps 60 --cool 20
"""
import argparse, sys
import numpy as np, torch as t
sys.path.insert(0, ".")
import hagi.models.optimal_lm as OM
from hagi.models.optimal_lm import HagiOptimalLM, HybridMuonAdamW

ap = argparse.ArgumentParser(); ap.add_argument("--steps", type=int, default=60); ap.add_argument("--cool", type=int, default=20); ap.add_argument("--lam", type=float, default=3e-3); a = ap.parse_args()
LEVELS_CPU = t.tensor([-3., -1., 1., 3.])
def LEVELS(dev): return LEVELS_CPU.to(dev)
def soft_entropy(W, tau=0.25):
    s = W.abs().amax(dim=1, keepdim=True).clamp_min(1e-8) / 3.0     # per-row scale -> levels ±3s
    z = (W / s).unsqueeze(-1)                                          # (rows, cols, 1)
    d = -(z - LEVELS(W.device)).abs() / tau                                      # distance to levels
    p = t.softmax(d, dim=-1)                                           # soft assignment
    m = p.mean(dim=1)                                                  # row histogram (levels)
    H = -(m * (m + 1e-12).log()).sum(-1)                               # nats per row
    return H.sum(), H
def hard_bytes(W):
    s = W.abs().amax(dim=1, keepdim=True).clamp_min(1e-8) / 3.0
    q = ((W / s).unsqueeze(-1) - LEVELS(W.device)).abs().argmin(-1)
    out = 0
    for r in range(q.shape[0]):
        cnt = t.bincount(q[r], minlength=4).float(); p = cnt / cnt.sum(); p = p[p > 0]
        out += float(-(p * p.log()).sum()) / np.log(2) / 8
    return out
def train(lam):
    t.manual_seed(0); rng = np.random.default_rng(0); m = HagiOptimalLM()
    tmpl = rng.integers(0, 256, 32); data = np.tile(tmpl, 128)
    for _ in range(200): data[rng.integers(0, len(data))] = rng.integers(0, 256)
    opt = HybridMuonAdamW(*m.matrix_and_vec_params(), lr_muon=0.0, lr_adam=3e-3, momentum=0.0, wd=1e-4); opt.names = m.param_names()
    mats = [p for p in m.params() if p.ndim == 2]
    for st in range(a.steps):
        x = t.as_tensor(np.stack([data[i:i + 32] for i in range(0, 2048, 32)])).long()
        y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(0, 2048, 32)])).long().to(m.device)
        opt.zero_grad()
        loss = t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1))
        if lam > 0 and st >= a.steps - a.cool:
            Hs = sum(soft_entropy(p)[0] for p in mats); loss = loss + lam * Hs
        loss.backward(); opt.step()
    x = t.as_tensor(np.stack([data[i:i + 32] for i in range(3000, 4000, 32)])).long().to(m.device)
    y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(3000, 4000, 32)])).long().to(m.device)
    with t.no_grad(): ce = float(t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)))
    qb, nb = OM.quantize_model(m, bits=2, use_had=True); OM.dequantize_into(m, qb)
    with t.no_grad(): ceq = float(t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)))
    hb = sum(hard_bytes(p.detach()) for p in mats)
    return ce, ceq, nb, hb
for lam in (0.0, a.lam):
    ce, ceq, nb, hb = train(lam)
    print(f"lam {lam:.0e}: held-out CE fp32 {ce:.4f} | CE quantised {ceq:.4f} | export bytes {nb} | coded-bytes lower bound (2-bit entropy) {hb:.0f} B")

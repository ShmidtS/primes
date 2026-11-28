"""A/B for PROPOSAL 27: asymmetric init of a grown depth block (eps*sign on W_down)
vs the zero init of grow_depth. Two seeds; reports holdout CE before/after growth
and the first-step gradient norm on the new block's W_up (pairGrad_u_at_eps).
Run from HAGI_v2's root:  HAGI_OLD_GATE=0 python C:/primes/scripts/ab_grow_init.py
"""
import sys, numpy as np, torch as t
sys.path.insert(0, ".")
from hagi.models.optimal_lm import HagiOptimalLM, HybridMuonAdamW, grow_depth

def make_opt(m):
    o = HybridMuonAdamW(*m.matrix_and_vec_params(), lr_muon=0.0, lr_adam=3e-3, momentum=0.0, wd=1e-4)
    o.names = m.param_names(); return o

def data_for(seed):
    rng = np.random.default_rng(seed); tmpl = rng.integers(0, 256, 32); d = np.tile(tmpl, 128)
    for _ in range(300): d[rng.integers(0, len(d))] = rng.integers(0, 256)
    return d

def batches(d, n, rng):
    ix = rng.integers(0, 2048, n)
    x = t.as_tensor(np.stack([d[i:i + 32] for i in ix])).long(); return x[:, :-1].contiguous(), x[:, 1:].contiguous()

def holdout_ce(m, d):
    with t.no_grad():
        x = t.as_tensor(np.stack([d[i:i + 32] for i in range(3000, 4000, 32)])).long().to(m.device)
        return float(t.nn.functional.cross_entropy(m.forward_seq(x[:, :-1].contiguous()).reshape(-1, 256), x[:, 1:].reshape(-1)))

def run(seed, eps, grow=True):
    t.manual_seed(seed); rng = np.random.default_rng(seed); d = data_for(seed)
    m = HagiOptimalLM(); opt = make_opt(m)
    for _ in range(150):
        x, y = batches(d, 16, rng); x, y = x.to(m.device), y.to(m.device)
        opt.zero_grad(); t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)).backward(); opt.step()
    ce_before = holdout_ce(m, d)
    if grow: grow_depth(m)
    opt = make_opt(m)
    if grow:
     Wg, Wu, Wd = m.blocks[-1]
    if grow and eps > 0:
        with t.no_grad(): Wd.copy_(eps * t.sign(t.randn(Wd.shape, device=Wd.device)))
    # first step on the grown model: gradient norm on the new W_up
    x, y = batches(d, 16, rng); x, y = x.to(m.device), y.to(m.device)
    opt.zero_grad(); t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)).backward()
    g_up = float(Wu.grad.norm()) if grow else float('nan'); opt.step()
    for _ in range(149):
        x, y = batches(d, 16, rng); x, y = x.to(m.device), y.to(m.device)
        opt.zero_grad(); t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)).backward(); opt.step()
    return ce_before, holdout_ce(m, d), g_up

if __name__ == "__main__":
    for eps, grow in ((0.0, False), (0.0, True), (1e-3, True)):
        res = [run(s, eps, grow) for s in (0, 1)]
        for s, (b, a, g) in zip((0, 1), res):
            print(f"eps={eps:.0e} grow={grow} seed={s}: CE before grow {b:.4f} -> after 150 steps {a:.4f}; first-step grad_W_up = {g:.4f}")

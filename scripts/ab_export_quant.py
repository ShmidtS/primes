"""A/B for PROPOSALS 25b (gauge balance at export) and 29 (per-row stage count).

Run from HAGI_v2's root (read-only use of its code):
    HAGI_OLD_GATE=0 python C:/primes/scripts/ab_export_quant.py --steps 60
Prints one row per variant: CE (fp32 model vs dequantised), export bytes,
per-row max |W|. Numbers are the acceptance evidence, not the assertion.
"""
import argparse, sys
import numpy as np, torch as t
sys.path.insert(0, ".")
from hagi.models.optimal_lm import HagiOptimalLM, HybridMuonAdamW, quant_per_row, dequant_per_row, gauge_balance

def ce(model, x, y):
    with t.no_grad():
        lg = model.forward_seq(x)
        return float(t.nn.functional.cross_entropy(lg.reshape(-1, 256), y.reshape(-1)))

def snapshot(model):
    return {n: p.detach().clone() for n, p in model.__dict__.items() if isinstance(p, t.nn.Parameter)}

def restore(model, snap):
    with t.no_grad():
        for n, v in snap.items(): getattr(model, n).copy_(v)

def export_ce(model, x, y, bits=2, mixed=False, use_had=True, rows2=None):
    snap = snapshot(model); nbytes, n2 = 0, 0; clip = 0; tot = 0
    for name, p in model.__dict__.items():
        if not isinstance(p, t.nn.Parameter) or p.ndim != 2: continue
        W = p.detach().cpu().numpy()
        rotate_rows = (name != "emb") and not (mixed and COLS_ONLY)
        par, Q = quant_per_row(W, bits=bits, use_had=use_had, rotate_rows=rotate_rows)
        if mixed and not rotate_rows:   # per-row stages need no row rotation
            R = W - dequant_per_row(par, Q)
            contrib = (R ** 2).sum(1)
            idx = np.flatnonzero(contrib > 4 * contrib.min()) if rows2 is None else np.argsort(-contrib)[:min(rows2, len(contrib))]
            if len(idx):
                par2, Q2 = quant_per_row(R[idx], bits=bits, use_had=use_had, rotate_rows=rotate_rows)
                n2 += len(idx)
                deq = dequant_per_row(par, Q); deq[idx] += dequant_per_row(par2, Q2)
                with t.no_grad(): getattr(model, name).copy_(t.as_tensor(deq, dtype=p.dtype).to(p.device))
                nbytes += Q.size // 4 + par["scales"].nbytes + Q2.size // 4 + par2["scales"].nbytes
                continue
        with t.no_grad(): getattr(model, name).copy_(t.as_tensor(dequant_per_row(par, Q), dtype=p.dtype).to(p.device))
        nbytes += Q.size // 4 + par["scales"].nbytes
        clip += int((Q >= 7).sum()) if bits != 2 else 0; tot += Q.size
    out = ce(model, x, y), nbytes, n2, clip
    restore(model, snap)
    return out

COLS_ONLY = False
if __name__ == "__main__":
    ap = argparse.ArgumentParser(); ap.add_argument("--steps", type=int, default=60); ap.add_argument("--wd", type=float, default=1e-4); ap.add_argument("--bits", type=int, default=2); ap.add_argument("--sweep", action="store_true", help="CE vs number of emb rows given a 2nd stage"); ap.add_argument("--cols-only", action="store_true", help="mixed: drop the row rotation so per-row stages stay valid on 2-D matrices")
    a = ap.parse_args(); COLS_ONLY = a.cols_only
    t.manual_seed(0); rng = np.random.default_rng(0)
    m = HagiOptimalLM()
    # structured byte stream: a 32-byte template repeated with occasional mutations (learnable)
    tmpl = rng.integers(0, 256, 32); data = np.tile(tmpl, 128)
    for _ in range(200): data[rng.integers(0, len(data))] = rng.integers(0, 256)
    opt = HybridMuonAdamW(*m.matrix_and_vec_params(), lr_muon=0.0, lr_adam=3e-3, momentum=0.0, wd=a.wd); opt.names = m.param_names()
    for s in range(a.steps):
        x = t.as_tensor(np.stack([data[i:i + 32] for i in range(0, 2048, 32)])).long()
        y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(0, 2048, 32)])).long().to(m.device)
        opt.zero_grad(); t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)).backward(); opt.step()
    x = t.as_tensor(np.stack([data[i:i + 32] for i in range(3000, 4000, 32)])).long().to(m.device)
    y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(3000, 4000, 32)])).long().to(m.device)
    base = ce(m, x, y)
    q0, b0, _, c0 = export_ce(m, x, y, bits=a.bits, mixed=False)
    snap0 = snapshot(m); ginfo = gauge_balance(m); qg, bg, _, cg = export_ce(m, x, y, bits=a.bits, mixed=False); restore(m, snap0)
    qm, bm, r2, _ = export_ce(m, x, y, bits=a.bits, mixed=(a.bits == 2))
    print(f"[wd={a.wd} steps={a.steps}] gauge max_log_shift swiglu={ginfo.get('max_log_shift_swiglu'):.3f} bigram={ginfo.get('max_log_shift_bigram'):.3f}")
    print(f"fp32 CE {base:.4f} | trits no-gauge {q0:.4f} ({b0} B) | gauge {qg:.4f} ({bg} B) | mixed-precision rows {qm:.4f} ({bm} B, +{r2} rows @2 stages)")
    print(f"clip-saturated levels (bits=4 only): no-gauge {c0}, gauge {cg}")
    if a.sweep:
        for k in (32, 64, 128, 256):
            qk, bk, _, _ = export_ce(m, x, y, bits=2, mixed=True, rows2=k)
            print(f"  emb rows @2 stages {k:4d}: CE {qk:.4f}, bytes {bk} (+{bk - b0})")
    print("ACCEPT 25b if gauge <= no-gauge; ACCEPT 29 if mixed < no-gauge at comparable bytes")

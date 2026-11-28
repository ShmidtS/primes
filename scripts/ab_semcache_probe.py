"""SEMCACHE probe for HAGI_v2 (Hagi/Information/SemCache.lean; cmix-neif-2.0 4.1).

Question: where the model is unsure, does a kNN over its own hidden states
(past positions -> next byte) beat the model when mixed in? Memory = past
(hidden, next byte) pairs of the same stream, i.e. decoder-reconstructible.
Run from HAGI_v2's root (read-only use of its code):
    PYTHONIOENCODING=utf-8 HAGI_OLD_GATE=0 python C:/primes/scripts/ab_semcache_probe.py --steps 60
"""
import argparse, sys
import numpy as np, torch as t
sys.path.insert(0, ".")
from hagi.models.optimal_lm import HagiOptimalLM, HybridMuonAdamW

ap = argparse.ArgumentParser(); ap.add_argument("--steps", type=int, default=60); ap.add_argument("--lam", type=float, default=0.3); ap.add_argument("--data", default="tmpl"); a = ap.parse_args()
t.manual_seed(0); rng = np.random.default_rng(0)
m = HagiOptimalLM()
if a.data == "tmpl":
    tmpl = rng.integers(0, 256, 32); data = np.tile(tmpl, 128)
    for _ in range(200): data[rng.integers(0, len(data))] = rng.integers(0, 256)
elif a.data == "text":  # Zipf-ish bytes: structure without periodicity
    pr = 1.0 / np.arange(1, 257); pr /= pr.sum(); data = rng.choice(256, size=8192, p=pr).astype(np.uint8)
else:
    data = rng.integers(0, 256, 8192).astype(np.uint8)
opt = HybridMuonAdamW(*m.matrix_and_vec_params(), lr_muon=0.0, lr_adam=3e-3, momentum=0.0, wd=1e-4); opt.names = m.param_names()
for s in range(a.steps):
    x = t.as_tensor(np.stack([data[i:i + 32] for i in range(0, 2048, 32)])).long()
    y = t.as_tensor(np.stack([data[i + 1:i + 33] for i in range(0, 2048, 32)])).long().to(m.device)
    opt.zero_grad(); t.nn.functional.cross_entropy(m.forward_seq(x).reshape(-1, 256), y.reshape(-1)).backward(); opt.step()

# held-out stream, one long window; memory = earlier positions of the same stream
seq = np.frombuffer(data[3000:6000], np.uint8).astype(np.int64); k = m.k
starts = np.arange(0, len(seq) - k - 1, k); X = np.stack([seq[i:i + k] for i in starts]); Y = seq[starts + k]
cap = {}; lg = m.forward_seq(t.as_tensor(X).long().to(m.device), capture=cap).detach()
H = cap[-1].cpu().numpy().astype(np.float64); P = t.softmax(lg[:, -1].float(), -1).cpu().numpy(); y = Y
pmax = P.max(1); unsure = pmax < 0.95
Hn = H - H.mean(0); Hn /= (np.linalg.norm(Hn, axis=1, keepdims=True) + 1e-9); S = Hn @ Hn.T
def knn_q(i, K=8):
    prev = np.arange(i); sim = S[i, prev]; idx = prev[np.argsort(-sim)[:K]]
    w = np.exp(sim[np.sort(np.argsort(-sim)[:K])] / 0.02) if i else np.zeros(0)
    q = np.zeros(256)
    if i:
        for j, wj in zip(idx, w / w.sum()): q[y[j]] += wj
    return q, (sim[idx].max() if i else 0.0)
ce_m = -np.log(P[np.arange(len(y)), y] + 1e-12)
sims = np.array([knn_q(i)[1] for i in range(len(y))])
print(f"max-cosine similarity: tmpl-periodic data has high s; quantiles 50/90/99%: {np.quantile(sims[1:], .5):.3f} {np.quantile(sims[1:], .9):.3f} {np.quantile(sims[1:], .99):.3f}")
for tau in (0.0, 0.3, 0.5, 0.7, 0.9, 0.95):
    ce_mix = ce_m.copy()
    for i in range(1, len(y)):
        q, sm = knn_q(i); lam = a.lam * max(sm, 0.0) if sm > tau else 0.0
        ce_mix[i] = -np.log((1 - lam) * P[i][y[i]] + lam * q[y[i]] + 1e-12)
    print(f"tau {tau:.2f}: CE model {ce_m.mean():.4f} -> mix {ce_mix.mean():.4f} ({ce_mix.mean() - ce_m.mean():+.4f}), gated positions {int((sims > tau).sum())}/{len(y)}")

# --- self-calibrated weight: lambda_t from decoder-verifiable accuracy of the kNN on the last N positions ---
def knn_pred(i, K=8):
    q, sm = knn_q(i); return (int(np.argmax(q)) if q.max() > 0 else -1), sm
for N in (16, 64):
    ce_cal = ce_m.copy(); hist = []  # (knn correct?, model correct?)
    for i in range(1, len(y)):
        recent = hist[-N:]
        acc_k = np.mean([h[0] for h in recent]) if recent else 0.0; acc_m = np.mean([h[1] for h in recent]) if recent else 0.0
        q, sm = knn_q(i); lam = a.lam * max(float(acc_k - acc_m), 0.0) * max(sm, 0.0)
        ce_cal[i] = -np.log((1 - lam) * P[i][y[i]] + lam * q[y[i]] + 1e-12)
        pk, _ = knn_pred(i); hist.append((pk == y[i], int(np.argmax(P[i])) == y[i]))
    print(f"calibrated N={N}: CE model {ce_m.mean():.4f} -> {ce_cal.mean():.4f} ({ce_cal.mean() - ce_m.mean():+.4f})")

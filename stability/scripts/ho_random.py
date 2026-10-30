"""Random jittered clouds: numerical abscissa in volume norms, spectral abscissa and Kreiss constants.

For every (D, kappa, jitter, n, seed, K, orientation):
  alpha     = max Re eig(L)                    (norm independent)
  omega_V   = numerical abscissa in the V norm, i.e. max eig of (VL + L^T V)/2 w.r.t. V  (V: 1/N and, in 1-D, dual volumes)
  Kreiss_V  = sup_t ||exp(tL)||_V over log-spaced t in [h/100, 20]
  nmin/nmax = neighbour counts
Usage: python3 ho_random.py D kappa jitter n1,n2,... K1,K2,... nseeds out.jsonl [geometric,aligned]
"""
import json
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import default_times, kreiss, sym_abscissa, volumes  # noqa: E402
from linop import build_operator, first_order_operator, make_cloud, neighbours  # noqa: E402

D, kappa, jit = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ns = [int(x) for x in sys.argv[4].split(",")]
Ks = [int(x) for x in sys.argv[5].split(",")]
nseeds, out = int(sys.argv[6]), sys.argv[7]
orients = sys.argv[8].split(",") if len(sys.argv) > 8 else ["geometric"]
a = [1.0] if D == 1 else [1.0, 0.5]
with open(out, "a") as f:
    for n in ns:
        for seed in range(nseeds):
            P, h = make_cloud(n, D, jit, seed)
            nb = neighbours(P, kappa * h)
            cnt = [len(j) for j, _ in nb]
            for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
                L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else build_operator(P, h, kappa, K, a, orient, nb=nb)
                ev = np.linalg.eigvals(L)
                rec = dict(D=D, kappa=kappa, jitter=jit, n=n, N=len(P), h=h, seed=seed, K=K, orient=orient,
                           nmin=min(cnt), nmax=max(cnt), alpha=float(ev.real.max()), alpha_h=float(ev.real.max() * h))
                for kind in (["uniform", "dual"] if D == 1 else ["uniform"]):
                    V = volumes(P, h, kind)
                    rec["omega_" + kind] = float(sym_abscissa(L, V))
                    rec["omega_h_" + kind] = float(sym_abscissa(L, V) * h)
                    if ev.real.max() * h < 1e-2:
                        rec["kreiss_" + kind] = float(kreiss(L, V, default_times(h)))
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print({k: (round(v, 6) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)

"""Diagonal Lyapunov weights, decided exactly instead of by the SDP of ho_lyapunov.py.

Since L 1 = 0, every diagonal H with M = H L + L^T H <= 0 has 1^T M 1 = 2 1^T H L 1 = 0, hence M 1 = 0, i.e.
L^T H 1 = 0: diag(H) is a multiple of the left null vector pi of L. The feasible set of the SDP is therefore at most one
ray (empty interior, which is why SCS returns "optimal_inaccurate"), and
  * a diagonal Lyapunov weight exists  iff  pi > 0 and the pi-symmetric part of L is <= 0 (omega_pi <= 0),
  * the minimal spread is then exactly rho = max(pi) / min(pi).
This script computes pi, its sign, omega_pi * h and rho on the clouds of ho_lyapunov.py (omega = 0) and decides
feasibility with the round-off threshold |omega_pi h| <= tol (default 1e-12).
Usage: python3 ho_lyapunov_exact.py D kappa jitter n1,n2,... K1,K2,... nseeds out.jsonl [geometric,aligned] [tol]
"""
import json
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import sym_abscissa  # noqa: E402
from linop import build_operator, first_order_operator, make_cloud, neighbours  # noqa: E402

D, kappa, jit = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ns = [int(x) for x in sys.argv[4].split(",")]
Ks = [int(x) for x in sys.argv[5].split(",")]
nseeds, out = int(sys.argv[6]), sys.argv[7]
orients = sys.argv[8].split(",") if len(sys.argv) > 8 else ["geometric"]
tol = float(sys.argv[9]) if len(sys.argv) > 9 else 1e-12
a = [1.0] if D == 1 else [1.0, 0.5]

with open(out, "a") as f:
    for n in ns:
        for seed in range(nseeds):
            P, h = make_cloud(n, D, jit, seed)
            nb = neighbours(P, kappa * h)
            for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
                L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else build_operator(P, h, kappa, K, a, orient, nb=nb)
                _, _, vt = sl.svd(L.T)
                pi = vt[-1]
                pi = pi / pi.sum()
                positive = bool(pi.min() > 0)
                rec = dict(D=D, kappa=kappa, jitter=jit, n=n, N=len(P), seed=seed, K=K, orient=orient,
                           pi_positive=positive, null_resid=float(np.abs(L.T @ pi).max() / np.abs(pi).max()))
                if positive:
                    om = sym_abscissa(L, pi) * h
                    rec.update(omega_pi_h=float(om), rho=float(pi.max() / pi.min()), feasible=bool(om <= tol))
                else:
                    rec.update(feasible=False)
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print(rec, flush=True)

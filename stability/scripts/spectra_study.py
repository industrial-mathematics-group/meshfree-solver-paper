"""Spectral abscissa of the linear semi-discrete operator on periodic (perturbed) clouds.

Usage: python3 spectra_study.py D kappa jitter n1,n2,... K1,K2,... nseeds out.jsonl [geometric,aligned]
For every cloud and design order K (no MOOD, no limiter, the given orientations for K >= 2,
the aligned first-order operator for K = 1) it records the spectral abscissa alpha = max Re(lambda),
alpha*h, the frequency |Im lambda| of the rightmost eigenvalue, the inverse participation ratio of its
eigenvector (1/N: spread out, 1: one particle), and ||exp(tL)||_2 at t = 1 if alpha*h < 1e-2.
Advection velocity a = 1 (1-D), a = (1, 0.5) (2-D).
"""
import json
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
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
            nmin = min(len(j) for j, _ in nb)
            for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
                try:
                    L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else \
                        build_operator(P, h, kappa, K, a, orient, nb=nb)
                except np.linalg.LinAlgError:
                    continue
                ev, V = np.linalg.eig(L)
                k = int(np.argmax(ev.real))
                v = np.abs(V[:, k]) ** 2
                v /= v.sum()
                rec = dict(D=D, orient=orient, kappa=kappa, jitter=jit, n=n, N=len(P), h=h, seed=seed, K=K, nmin=nmin,
                           alpha=float(ev.real[k]), alpha_h=float(ev.real[k] * h), freq=float(abs(ev.imag[k])),
                           ipr=float((v**2).sum()))
                if ev.real[k] * h < 1e-2:
                    rec["growth_t1"] = float(np.linalg.norm(sl.expm(L), 2))
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print(rec, flush=True)

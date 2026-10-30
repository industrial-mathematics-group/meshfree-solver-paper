"""Bloch (Floquet) analysis of periodic clouds: a jittered supercell of m points per direction, repeated periodically.

The refinement family of a periodic cloud is stable iff its Bloch symbols Lhat(theta), theta in [-pi, pi]^D, satisfy
max Re eig <= 0 and sup_theta sup_t ||exp(t Lhat(theta))|| < infinity (Theorem in the note). This script samples theta,
and records   alpha_h = max_theta max Re eig(Lhat) * h,   kreiss = max_theta sup_t ||exp(t Lhat(theta))||_2.
Usage: python3 ho_bloch.py D kappa jitter m1,m2,... K1,K2,... nseeds ntheta out.jsonl [geometric,aligned]
"""
import json
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import bloch_symbols  # noqa: E402

D, kappa, jit = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ms = [int(x) for x in sys.argv[4].split(",")]
Ks = [int(x) for x in sys.argv[5].split(",")]
nseeds, ntheta, out = int(sys.argv[6]), int(sys.argv[7]), sys.argv[8]
orients = sys.argv[9].split(",") if len(sys.argv) > 9 else ["geometric"]
a = [1.0] if D == 1 else [1.0, 0.5]


def kreiss_sym(S, h):
    ts = np.logspace(-2, 3, 26) * h          # dimensionless times t/h in [1e-2, 1e3]
    ev, X = np.linalg.eig(S)
    Xi = np.linalg.inv(X)
    return max(np.linalg.norm((X * np.exp(t * ev)[None, :]) @ Xi, 2) for t in ts)


with open(out, "a") as f:
    for m in ms:
        for seed in range(nseeds):
            rng = np.random.default_rng(1000 + seed)
            g = (np.arange(m) + 0.5) / m
            P0 = np.stack(np.meshgrid(*([g] * D), indexing="ij"), axis=-1).reshape(-1, D)
            P0 = np.mod(P0 + jit / m * (2 * rng.random(P0.shape) - 1), 1.0)
            if D == 1:
                thetas = np.linspace(-np.pi, np.pi, ntheta, endpoint=False)
            else:
                t1 = np.linspace(-np.pi, np.pi, ntheta, endpoint=False)
                thetas = np.array([(x, y) for x in t1 for y in t1])
            for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
                syms, h = bloch_symbols(P0, kappa, K, a, orient, thetas)
                alph = [np.linalg.eigvals(S).real.max() for S in syms]
                kmax, kworst = 0.0, None
                for S, th in zip(syms, thetas):
                    k = kreiss_sym(S, h)
                    if k > kmax:
                        kmax, kworst = k, th
                i = int(np.argmax(alph))
                rec = dict(D=D, kappa=kappa, jitter=jit, m=m, seed=seed, K=K, orient=orient, h=h, ntheta=len(thetas),
                           alpha_h=float(alph[i] * h), theta_worst=np.atleast_1d(thetas[i]).tolist(),
                           alpha0_h=float(alph[0] * h) if D == 1 else None, kreiss=float(kmax),
                           theta_kreiss=np.atleast_1d(kworst).tolist())
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print({k: (round(v, 7) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)

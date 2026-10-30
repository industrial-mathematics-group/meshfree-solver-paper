"""Diagonal Lyapunov weights for the high-order operator: does a weighted l2 norm exist in which L is contractive?

Solves the SDP   minimise rho  s.t.  1 <= H_i <= rho (diagonal),  H L + L^T H  <=  2 omega H   (omega given, default 0),
on jittered clouds, and compares with the first-order case (where H = pi, the stationary distribution, is feasible with
omega = 0). Infeasible (or rho growing with N) means that no diagonal weight makes the energy method work.
Usage: python3 ho_lyapunov.py D kappa jitter n1,n2,... K1,K2,... nseeds omega out.jsonl [geometric,aligned]
"""
import json
import sys

import cvxpy as cp
import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import build_operator, first_order_operator, make_cloud, neighbours  # noqa: E402

D, kappa, jit = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ns = [int(x) for x in sys.argv[4].split(",")]
Ks = [int(x) for x in sys.argv[5].split(",")]
nseeds, omega, out = int(sys.argv[6]), float(sys.argv[7]), sys.argv[8]
orients = sys.argv[9].split(",") if len(sys.argv) > 9 else ["geometric"]
a = [1.0] if D == 1 else [1.0, 0.5]


def diag_lyapunov(L, omega, h):
    N = len(L)
    Ls = L * h                       # dimensionless
    hvar = cp.Variable(N)
    rho = cp.Variable()
    H = cp.diag(hvar)
    M = H @ Ls + Ls.T @ H - 2 * omega * h * H
    cons = [hvar >= 1, hvar <= rho, M << 0]
    prob = cp.Problem(cp.Minimize(rho), cons)
    try:
        prob.solve(solver=cp.SCS, eps=1e-7, max_iters=50000)
    except Exception as e:  # noqa: BLE001
        return dict(status="error:" + str(e)[:40])
    res = dict(status=prob.status)
    if hvar.value is not None:
        hv = np.maximum(hvar.value, 1e-12)
        Hm = np.diag(hv)
        Msym = Hm @ Ls + Ls.T @ Hm - 2 * omega * h * Hm
        res.update(rho=float(hv.max() / hv.min()), resid=float(np.linalg.eigvalsh(Msym).max()))
    return res


with open(out, "a") as f:
    for n in ns:
        for seed in range(nseeds):
            P, h = make_cloud(n, D, jit, seed)
            nb = neighbours(P, kappa * h)
            for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
                L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else build_operator(P, h, kappa, K, a, orient, nb=nb)
                alpha = np.linalg.eigvals(L).real.max()
                rec = dict(D=D, kappa=kappa, jitter=jit, n=n, N=len(P), seed=seed, K=K, orient=orient, omega=omega,
                           alpha_h=float(alpha * h))
                rec.update(diag_lyapunov(L, omega, h))
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print(rec, flush=True)

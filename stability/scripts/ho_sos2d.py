"""Sum-of-squares decomposition of the dissipation form of the 2-D lattice scheme (the 2-D substitute for Fejer-Riesz).

f(theta) = -(1/N) symbol of (L + L^T) (weight 1/N = h^2 cancels the 1/h) = sum_k c_k e^{i k.theta}, k in a box.
Seeks a Gram matrix G >= 0 over the monomials e^{i m.theta}, m in [-r, r]^2, with sum_{m - m' = k} G_{m m'} = c_k,
which gives  -(V L + L^T V) = sum_j sum_s (sum_m b_{s,m} u_{j+m})^2  with G = sum_s b_s b_s^T.
Usage: python3 ho_sos2d.py K1,K2 out.md [orients] [r]
"""
import sys

import cvxpy as cp
import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import build_operator  # noqa: E402

Ks = [int(v) for v in sys.argv[1].split(",")]
out = sys.argv[2]
orients = sys.argv[3].split(",") if len(sys.argv) > 3 else ["geometric"]
r_user = int(sys.argv[4]) if len(sys.argv) > 4 else None
kappa, n = 2.5, 16
h = 1.0 / n
g = (np.arange(n) + 0.5) * h
P = np.stack(np.meshgrid(g, g, indexing="ij"), axis=-1).reshape(-1, 2)
with open(out, "a") as f:
    for K in Ks:
        for orient in orients:
            L = build_operator(P, h, kappa, K, [1.0, 0.5], orient) * h
            S = -(L + L.T)
            row = S[0]
            c = {}
            for j in range(n * n):
                if abs(row[j]) > 1e-14:
                    k = (((j // n) + n // 2) % n - n // 2, ((j % n) + n // 2) % n - n // 2)
                    c[k] = row[j]
            d = max(max(abs(k[0]), abs(k[1])) for k in c)
            r = r_user if r_user else d
            mons = [(i, j) for i in range(-r, r + 1) for j in range(-r, r + 1)]
            idx = {m: i for i, m in enumerate(mons)}
            M = len(mons)
            # exact matching of the coefficients, maximal minimal eigenvalue of the Gram matrix
            G = cp.Variable((M, M), symmetric=True)
            lam = cp.Variable()
            cons = [G >> lam * np.eye(M)]
            keys = sorted(set([(i, j) for i in range(-2 * r, 2 * r + 1) for j in range(-2 * r, 2 * r + 1)]))
            Amat, rhs = [], []
            for k in keys:
                row = np.zeros((M, M))
                for m in mons:
                    mm = (m[0] - k[0], m[1] - k[1])
                    if mm in idx:
                        row[idx[m], idx[mm]] += 1.0
                if row.any():
                    Amat.append(row.reshape(-1))
                    rhs.append(c.get(k, 0.0))
            Amat = np.array(Amat)
            cons.append(Amat @ cp.vec(G, order="C") == np.array(rhs))
            prob = cp.Problem(cp.Maximize(lam), cons)
            prob.solve(solver=cp.CLARABEL)
            Gv = 0.5 * (G.value + G.value.T)
            ev = np.linalg.eigvalsh(Gv)
            resid = np.abs(Amat @ Gv.reshape(-1) - np.array(rhs)).max()
            line = "| %d | %s | d=%d | r=%d | M=%d | %s | max|residual| = %.2e | min eig G = %.2e | max eig G = %.2e |" % (
                K, orient, d, r, M, prob.status, resid, ev[0], ev[-1])
            f.write(line + "\n")
            f.flush()
            print(line, flush=True)
            np.save(out.replace(".md", "_K%d_%s_G.npy" % (K, orient)), Gv)

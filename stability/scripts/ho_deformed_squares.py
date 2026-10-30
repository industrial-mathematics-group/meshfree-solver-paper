"""Local-squares lemma on smoothly deformed 1-D lattices (no defects).

With the Jacobian-volume weight V_i = phi'(s_i) h and the Fejer-Riesz factor b(g) of the uniform lattice of spacing g h,
the claim is   u^T (V L + L^T V) u + sum_j B_j^{(g_j)}(u) <= C h |u|^2,  B_j^{(g)}(u) = (sum_k b_k(g) u_{j+k})^2,
i.e. the deformed dissipation form is bounded by the frozen local squares up to O(h).  Records the largest eigenvalue of
the residual R = V L + L^T V + sum_j B_j in units of h (should stay bounded as n grows) and the V-numerical abscissa.
Usage: python3 ho_deformed_squares.py A n1,n2,... K1,K2,... out.md
"""
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import deformed_cloud, jacobian_volumes  # noqa: E402
from ho_fr import local_squares_1d  # noqa: E402
from linop import build_operator  # noqa: E402

A = float(sys.argv[1])
ns = [int(v) for v in sys.argv[2].split(",")]
Ks = [int(v) for v in sys.argv[3].split(",")]
out = sys.argv[4]
kappa = 2.5
with open(out, "a") as f:
    f.write("| A | n | K | max eig(R)/h | min eig(R)/h | omega_V h | omega_V |\n|---|---|---|---|---|---|---|\n")
    for K in Ks:
        cache = {}
        for n in ns:
            P, h, S = deformed_cloud(n, 1, A)
            V = jacobian_volumes(S, A, h)
            L = build_operator(P, h, kappa, K, [1.0], "geometric")
            N = len(P)
            R = np.diag(V) @ L + L.T @ np.diag(V)
            g = 1.0 + A * np.cos(2 * np.pi * S[:, 0])
            for j in range(N):
                gj = round(float(g[j]), 4)
                if gj not in cache:
                    cache[gj] = local_squares_1d(K, "geometric", kappa, gj)[0]
                b = cache[gj]
                e = np.zeros(N)
                for k in range(len(b)):
                    e[(j + k) % N] += b[k]
                R += np.outer(e, e)
            ev = np.linalg.eigvalsh(0.5 * (R + R.T)) / h
            om = sl.eigh(0.5 * (np.diag(V) @ L + L.T @ np.diag(V)), np.diag(V), eigvals_only=True)[-1]
            line = "| %g | %d | %d | %.4f | %.4f | %.2e | %.4f |" % (A, n, K, ev[-1], ev[0], om * h, om)
            f.write(line + "\n")
            f.flush()
            print(line, flush=True)

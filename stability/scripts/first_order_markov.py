"""First-order aligned scheme for linear advection as a Markov generator.

L1 U_i = sum_j q_ij (U_j - U_i), q_ij = sum_d (|a_d| |c_ij^(d)| - a_d c_ij^(d)) >= 0 (degree-one weights).
For periodic jittered lattices this script computes
  * the stationary density pi (pi^T L1 = 0, sum pi = 1) and the spread rho = max(N pi_i) / min(N pi_i),
    which is the square of the norm-equivalence constant between l2(pi) and the plain discrete L2 norm,
  * the truncation error of the first-order operator for u = sin(2 pi x_1) (max over particles),
  * the error of the semi-discrete solution at t = 1 (exact time integration by expm), max and L2.
Usage: python3 first_order_markov.py D jitter kappa n1,n2,... nseeds out.md
"""
import sys

import numpy as np
import scipy.linalg as sl
import scipy.sparse as sp
import scipy.sparse.linalg as spl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import derivative_weights, make_cloud, neighbours  # noqa: E402


def generator(P, h, kappa, a, nb):
    rows, cols, vals = [], [], []
    for i, (js, off) in enumerate(nb):
        c = derivative_weights(off, kappa * h, 1, h)
        q = (np.abs(a)[None, :] * np.abs(c) - a[None, :] * c).sum(1)
        rows += [i] * len(js) + [i]
        cols += list(js) + [i]
        vals += list(q) + [-q.sum()]
    return sp.csr_matrix((vals, (rows, cols)), shape=(len(P), len(P)))


if __name__ == "__main__":
    D, jit, kappa = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
    ns = [int(x) for x in sys.argv[4].split(",")]
    nseeds, out = int(sys.argv[5]), sys.argv[6]
    a = np.array([1.0] if D == 1 else [1.0, 0.5])
    lines = []
    for n in ns:
        for seed in range(nseeds):
            P, h = make_cloud(n, D, jit, seed)
            nb = neighbours(P, kappa * h)
            Q = generator(P, h, kappa, a, nb)
            N = len(P)
            # stationary density: solve Q^T pi = 0 with one equation replaced by sum(pi) = 1
            A = Q.T.tolil()
            A[0, :] = np.ones(N)
            b = np.zeros(N)
            b[0] = 1.0
            pi = spl.spsolve(A.tocsc(), b)
            rho = (N * pi).max() / (N * pi).min()
            u0 = np.sin(2 * np.pi * P[:, 0])
            tau = Q @ u0 + a[0] * 2 * np.pi * np.cos(2 * np.pi * P[:, 0])
            rec = dict(n=n, N=N, seed=seed, pimin=float(N * pi.min()), pimax=float(N * pi.max()), rho=float(rho),
                       trunc_max=float(np.abs(tau).max()), trunc_l2=float(np.sqrt((tau**2).mean())))
            if N <= 3000:
                U = sl.expm(Q.toarray()) @ u0
                ex = np.sin(2 * np.pi * (P[:, 0] - a[0]))
                rec["err_max"] = float(np.abs(U - ex).max())
                rec["err_l2"] = float(np.sqrt(((U - ex) ** 2).mean()))
            print(rec, flush=True)
            lines.append(rec)
    with open(out, "a") as f:
        for r in lines:
            f.write("| %d | %.2f | %.1f | %d | %d | %.3f | %.3f | %.3f | %.2e | %.2e | %s | %s |\n" % (
                D, jit, kappa, r["n"], r["seed"], r["pimin"], r["pimax"], r["rho"], r["trunc_max"], r["trunc_l2"],
                "%.2e" % r["err_max"] if "err_max" in r else "-", "%.2e" % r["err_l2"] if "err_l2" in r else "-"))

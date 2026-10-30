"""Corrector size of the first-order aligned operator on large periodic 1-D clouds (linear advection, a = 1).

Same quantities as first_order_corrector.py (beta_i, pi, beta_bar, corrector delta with Q delta = beta - beta_bar,
pi.delta = 0), but with neighbour search in a window of the sorted cloud and sparse assembly, so N = 1e5 is feasible.
Used for Observation "Drift": max|delta|/h grows like h^(-1/2), i.e. the corrector size is about h^(1/2).
Usage: python3 first_order_corrector_large.py jitter kappa n1,n2,... nseeds
"""
import sys

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import derivative_weights, make_cloud  # noqa: E402

jit, kappa = float(sys.argv[1]), float(sys.argv[2])
for n in [int(x) for x in sys.argv[3].split(",")]:
    for seed in range(int(sys.argv[4])):
        P, h = make_cloud(n, 1, jit, seed)
        xs = np.sort(P[:, 0])
        N = n
        rows, cols, vals, beta = [], [], [], np.zeros(N)
        W = int(kappa + 2 * jit + 2)
        for i in range(N):
            idx = (i + np.arange(-W, W + 1)) % N
            idx = idx[idx != i]
            d = xs[idx] - xs[i]
            d -= np.round(d)
            m = np.abs(d) <= kappa * h * (1 + 1e-12)
            idx, d = idx[m], d[m]
            c = derivative_weights(d[:, None], kappa * h, 1, h)[:, 0]
            q = np.abs(c) - c
            rows += [i] * len(idx) + [i]
            cols += list(idx) + [i]
            vals += list(q) + [-q.sum()]
            beta[i] = (np.abs(c) * d).sum()
        Q = sp.csr_matrix((vals, (rows, cols)), shape=(N, N))
        A = Q.T.tolil()
        A[0, :] = np.ones(N)
        b = np.zeros(N)
        b[0] = 1.0
        pi = spl.spsolve(A.tocsc(), b)
        bbar = pi @ beta
        M = sp.bmat([[Q, sp.csr_matrix(np.ones((N, 1)))], [sp.csr_matrix(pi[None, :]), None]]).tocsc()
        delta = spl.spsolve(M, np.concatenate([beta - bbar, [0.0]]))[:N]
        print(f"| {jit} | {kappa} | {n} | {seed} | {bbar:.3e} | {np.abs(delta).max() / h:.3f} | "
              f"{np.sqrt(pi @ delta**2) / h:.3f} | {pi.max() / pi.min():.2f} |", flush=True)

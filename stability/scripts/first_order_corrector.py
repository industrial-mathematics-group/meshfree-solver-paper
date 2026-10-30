"""Drift and corrector of the first-order aligned operator on periodic 1-D clouds (linear advection, a = 1).

beta_i = sum_j |c_ij| x_ij is the first moment of the dissipation weights (O(1) on irregular clouds, 0 on
lattices); the truncation error of the first-order operator is tau_i = |a| beta_i u'(x_i) + O(h).
The script reports the pi-mean beta_bar = sum_i pi_i beta_i (the drift error: the semi-discrete scheme
transports with the effective velocity a (1 - beta_bar sign(a)) ... see the note) and the corrector delta
with Q delta = |a| (beta - beta_bar), sum_i pi_i delta_i = 0, through max|delta|/h.
Usage: python3 first_order_corrector.py jitter kappa n1,n2,... nseeds
"""
import sys

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from first_order_markov import generator  # noqa: E402
from linop import derivative_weights, make_cloud, neighbours  # noqa: E402

jit, kappa = float(sys.argv[1]), float(sys.argv[2])
ns = [int(x) for x in sys.argv[3].split(",")]
nseeds = int(sys.argv[4])
a = np.array([1.0])
for n in ns:
    for seed in range(nseeds):
        P, h = make_cloud(n, 1, jit, seed)
        nb = neighbours(P, kappa * h)
        Q = generator(P, h, kappa, a, nb)
        N = len(P)
        beta = np.array([(np.abs(derivative_weights(off, kappa * h, 1, h)[:, 0]) * off[:, 0]).sum()
                         for js, off in nb])
        A = Q.T.tolil()
        A[0, :] = np.ones(N)
        b = np.zeros(N)
        b[0] = 1.0
        pi = spl.spsolve(A.tocsc(), b)
        bbar = pi @ beta
        # corrector: Q delta = beta - bbar, with pi.delta = 0 (bordered system)
        M = sp.bmat([[Q, sp.csr_matrix(np.ones((N, 1)))], [sp.csr_matrix(pi[None, :]), None]]).tocsc()
        sol = spl.spsolve(M, np.concatenate([beta - bbar, [0.0]]))
        delta = sol[:N]
        print(f"jitter={jit} kappa={kappa} n={n} seed={seed}: max|beta|={np.abs(beta).max():.3f} "
              f"beta_bar={bbar:.2e} max|delta|/h={np.abs(delta).max() / h:.3f} rms delta/h={np.sqrt(pi @ delta**2) / h:.3f}",
              flush=True)

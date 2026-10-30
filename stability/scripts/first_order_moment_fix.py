"""Moment-corrected dissipation for the first-order scheme (1-D test of the remedy in the stability note).

The Rusanov dissipation weights s|c_ij| have the first moment beta_i = sum_j |c_ij| x_ij, which is O(1) on irregular
clouds and causes an O(1) wave-speed error of the first-order scheme. Adding non-negative weights e_ij with
sum_j e_ij x_ij = -beta_i (here: on the farthest neighbour on the side opposite to beta_i) keeps all
off-diagonal coefficients non-negative (positivity, maximum principle) and removes the first moment.
Prints the effective speed and the rms error at T = 10 for u0 = sin(2 pi x), with and without the correction.
Usage: python3 first_order_moment_fix.py jitter kappa n1,n2,...
"""
import sys

import numpy as np
import scipy.sparse as sp
import scipy.sparse.linalg as spl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import derivative_weights, make_cloud, neighbours  # noqa: E402


def generator(P, h, kappa, a, nb, fix):
    rows, cols, vals = [], [], []
    for i, (js, off) in enumerate(nb):
        c = derivative_weights(off, kappa * h, 1, h)[:, 0]
        g = np.abs(c)
        if fix:
            beta = (g * off[:, 0]).sum()
            k = np.argmin(off[:, 0]) if beta > 0 else np.argmax(off[:, 0])
            g = g.copy()
            g[k] += -beta / off[k, 0]
        q = abs(a) * g - a * c
        assert (q >= -1e-12).all()
        rows += [i] * len(js) + [i]
        cols += list(js) + [i]
        vals += list(q) + [-q.sum()]
    return sp.csr_matrix((vals, (rows, cols)), shape=(len(P), len(P)))


jit, kappa = float(sys.argv[1]), float(sys.argv[2])
T = 10.0
for n in [int(x) for x in sys.argv[3].split(",")]:
    P, h = make_cloud(n, 1, jit, 0)
    nb = neighbours(P, kappa * h)
    x = P[:, 0]
    for fix in (False, True):
        Q = generator(P, h, kappa, 1.0, nb, fix)
        U = spl.expm_multiply(T * Q, np.sin(2 * np.pi * x))
        Mx = np.stack([np.sin(2 * np.pi * x), np.cos(2 * np.pi * x)], 1)
        (al, be), *_ = np.linalg.lstsq(Mx, U, rcond=None)
        shift = (np.arctan2(-be, al) / (2 * np.pi) - T) % 1.0
        shift = shift - 1.0 if shift > 0.5 else shift
        err = np.sqrt(np.mean((U - np.sin(2 * np.pi * (x - T))) ** 2))
        print(f"jitter={jit} kappa={kappa} n={n} corrected={fix}: a_eff-1={shift / T: .2e} rms error={err:.3e}",
              flush=True)

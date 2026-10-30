"""High-precision check of the positive Bloch spectral abscissa of a K = 2 supercell at jitter 0.2h (1-D, kappa = 2.5).

Rebuilds the pattern of ho_bloch.py (seed 1000 + 0), samples 2001 values of theta, and at the worst theta recomputes the
eigenvalues of the m x m Bloch symbol with mpmath (40 digits); also reports the eigenvector condition number and the
number of theta with alpha*h > 1e-13.  Output: data/ho_bloch_mpcheck.md.
Usage: python3 ho_bloch_mpcheck.py
"""
import sys

import mpmath as mp
import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import bloch_symbols  # noqa: E402

mp.mp.dps = 40
print("| m | theta* | alpha h (float64) | alpha h (40 digits) | eigenvector condition | #theta with alpha h > 1e-13 (of 2001) |")
print("|---|---|---|---|---|---|")
for m in (16, 32):
    rng = np.random.default_rng(1000)
    g = (np.arange(m) + 0.5) / m
    P0 = np.mod(g[:, None] + 0.2 / m * (2 * rng.random((m, 1)) - 1), 1.0)
    th = np.linspace(-np.pi, np.pi, 2001)
    syms, h = bloch_symbols(P0, 2.5, 2, [1.0], "geometric", th)
    al = np.array([np.linalg.eigvals(S).real.max() for S in syms]) * h
    i = int(np.argmax(al))
    S = syms[i]
    ev, X = np.linalg.eig(S)
    j = int(np.argmax(ev.real))
    y = np.linalg.solve(X.T, np.eye(m)[:, j])
    cond = np.linalg.norm(X[:, j]) * np.linalg.norm(y) / abs(y @ X[:, j])
    E = mp.eig(mp.matrix(S.tolist()))[0]
    amp = float(max(mp.re(e) for e in E)) * h
    print(f"| {m} | {th[i]:.4f} | {al[i]:.4e} | {amp:.4e} | {cond:.4f} | {(al > 1e-13).sum()} |")

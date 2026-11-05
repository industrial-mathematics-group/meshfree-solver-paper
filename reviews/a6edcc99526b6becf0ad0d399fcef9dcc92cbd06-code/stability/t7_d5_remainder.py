"""d5_check.py discards the remainder of the deflation by (1 - x)^m.  Report the largest remainder relative to max|F|,
and an independent check of (D5): min over x of f(x)/(1-x)^m evaluated directly from the cosine series (no division)."""
import os, sys, numpy as np
from numpy.polynomial import chebyshev as C, polynomial as Pl
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
from ho_fr import lattice_rows
x = np.linspace(-1, 0.999, 20001)
for K, orient in [(2, "geometric"), (3, "geometric"), (4, "geometric"), (4, "aligned")]:
    m_exp = 2 if K in (2, 3) else 3
    rmax, qdir = 0.0, np.inf
    for g in np.linspace(0.85, 1.20, 141):
        ell, d = lattice_rows(K, orient, 2.5, g)
        c = np.array([-g * (ell[d + k] + ell[d - k]) for k in range(d + 1)]); c[0] = -2 * g * ell[d]
        F = C.cheb2poly(np.concatenate([[c[0]], 2 * c[1:]]))
        scale = np.abs(F).max()
        for _ in range(m_exp):
            F, r = Pl.polydiv(F, [1.0, -1.0]); rmax = max(rmax, np.abs(r).max() / scale)
        th = np.arccos(x)
        f = c[0] + 2 * sum(c[k] * np.cos(k * th) for k in range(1, d + 1))
        qdir = min(qdir, (f / (1 - x) ** m_exp).min())
    print(f"K={K} {orient}: max deflation remainder / max|F| = {rmax:.1e};  direct min_x<0.999 f/(1-x)^m = {qdir:.4e}")

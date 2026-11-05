# From the independent review of 3 Nov 2026 (reviews/meshfree-solver-paper/stability/), added 4 Nov 2026.
"""Note: Pl.polydiv(F, [1, -1]) divides by (1 - x).
(D4)/(D5) on 1-D frozen lattices of spacing g (kappa = 2.5): f_g(theta) = -2 g Re mu_g as a polynomial in x = cos theta,
deflate (1 - x)^m with m from the parity rule, report min over [-1, 1] of the quotient q_g (D5 constant) and the order m found
by ho_fr.fejer_riesz, for g on a fine grid in [0.85, 1.20]."""
import sys
import numpy as np
from numpy.polynomial import chebyshev as C, polynomial as Pl
sys.path.insert(0, sys.argv[1])
from ho_fr import lattice_rows, local_squares_1d
x = np.linspace(-1, 1, 20001)
for K, orient in [(2, "geometric"), (3, "geometric"), (4, "geometric"), (4, "aligned")]:
    m_exp = 2 if K in (2, 3) else 3
    qmin, ms, errs, nbs = np.inf, set(), [], set()
    for g in np.linspace(0.85, 1.20, 141):
        ell, d = lattice_rows(K, orient, 2.5, g)
        c = np.array([-g * (ell[d + k] + ell[d - k]) for k in range(d + 1)]); c[0] = -2 * g * ell[d]
        cheb = np.concatenate([[c[0]], 2 * c[1:]])
        F = C.cheb2poly(cheb)
        for _ in range(m_exp):
            F, r = Pl.polydiv(F, [1.0, -1.0])
        # numpy's [1, -1] is (1 - x): F = q (1 - x)^m, no sign change
        qmin = min(qmin, Pl.polyval(x, F).min())
        b, dd, m, err = local_squares_1d(K, orient, 2.5, g)
        ms.add(m); errs.append(err); nbs.add(d)
    print(f"K={K} {orient}: half-bandwidth d={sorted(nbs)}, FR order m found {sorted(ms)} (parity rule m={m_exp}), "
          f"min_g min_x q_g = {qmin:.4e}, max FR rel. error {max(errs):.1e}")

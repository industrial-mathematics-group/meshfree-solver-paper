"""The CFL bisection of lattice_symbols.cfl_max accepts max|R| <= 1 + 1e-12.  For RK2 and K = 4, 5 the amplification
excess at small theta is ~ (CFL theta)^4 / 8, below 1e-12 on a 4001-point grid; check what CFL_max RK2 becomes with a
strict criterion (|R| <= 1 + 1e-15) and with a finer grid near theta = 0."""
import os, sys, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
import lattice_symbols as ls
for kappa, K in [(2.5, 2), (2.5, 3), (2.5, 4), (2.5, 5), (3.5, 4)]:
    lam, norm, q = ls.symbol(1, kappa, K, [1.0], m=4001)
    c_def = ls.cfl_max(lam, norm, "RK2")
    exc = (np.abs(ls.R_rk(c_def / norm * lam, "RK2")) - 1).max()
    # theta near 0 with a log grid: does |R| > 1 there?
    P, h = ls.make_cloud(int(np.ceil(4 * kappa)) + 4, 1, 0.0)
    nb = ls.neighbours(P, kappa * h)
    L = ls.build_operator(P, h, kappa, K, [1.0], "geometric", nb=nb) if K > 1 else None
    off = P[:, 0] - P[0, 0]; off -= np.round(off); ints = np.round(off / h).astype(int)
    th = np.logspace(-4, 0, 2000)
    lam2 = (np.exp(1j * th[:, None] * ints[None, :]) * (L[0] * h)[None, :]).sum(1)
    z = c_def / norm * lam2
    exc2 = (np.abs(ls.R_rk(z, "RK2")) - 1).max()
    print(f"kappa={kappa} K={K}: CFL_max RK2 (tol 1e-12, 4001 pts) = {c_def:.3f}; at that CFL max(|R|-1) on 4001 grid = {exc:.1e}, "
          f"on log grid theta in [1e-4,1] = {exc2:.1e}")

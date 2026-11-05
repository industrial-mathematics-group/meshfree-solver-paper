"""Independent checks of scripts/stencil_diagnostics.py and the Monte Carlo fallback scripts.
Run from the repo root: python3 reviews/<name>/test_stencils.py"""
import os, sys, itertools, numpy as np
ROOT = os.environ.get("REPO", os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))
sys.path.insert(0, os.path.join(ROOT, "scripts"))
import stencil_diagnostics as sd
from fallback_positivity_lib import flux, lam, cons, pres

def check_polynomial_exactness():
    # derivative weights of degree q must differentiate every polynomial of degree <= q exactly
    for jit in (0.0, 0.2):
        P, L = sd.make_cloud(16, jit, 3)
        idx, off, m = sd.neighbour_table(P, L, 2.5)
        for q in (1, 2, 3):
            for intercept in (True, False):
                c = sd.derivative_weights(off, m, 2.5, q, intercept)
                worst = 0.0
                for a in sd.exponents(2, q):
                    val = np.prod(off ** np.array(a), axis=-1) * m          # p(x_j - x_i), p(0)=0
                    d0 = (c[..., 0] * val).sum(1); d1 = (c[..., 1] * val).sum(1)
                    ex0 = 1.0 if a == (1, 0) else 0.0; ex1 = 1.0 if a == (0, 1) else 0.0
                    worst = max(worst, np.abs(d0 - ex0).max(), np.abs(d1 - ex1).max())
                print(f"jitter {jit} q={q} intercept={intercept}: max error on monomials of degree<=q: {worst:.1e}")
                assert worst < 1e-6
                if intercept:   # with a constant term the weights also annihilate constants
                    assert np.abs(c.sum(1)).max() < 1e-8

def check_exponents():
    assert sd.exponents(2, 1) == [(1, 0), (0, 1)]
    assert len(sd.exponents(2, 3)) == 9 and len(sd.exponents(3, 2)) == 9

def check_neighbour_symmetry():
    P, L = sd.make_cloud(20, 0.2, 5); idx, off, m = sd.neighbour_table(P, L, 2.5)
    S = {(i, j) for i in range(len(P)) for j in idx[i][m[i]]}
    assert all((j, i) in S for (i, j) in S)
    d = np.linalg.norm(off[m], axis=1); assert d.max() <= 2.5 + 1e-9 and d.min() > 0

def check_flux_helpers():
    U = cons(1.3, 0.4, -0.7, 2.1)
    assert abs(pres(U) - 2.1) < 1e-12
    r, u, v, p, g = 1.3, 0.4, -0.7, 2.1, 1.4
    E = p/(g-1) + 0.5*r*(u*u+v*v)
    assert np.allclose(flux(U, 0), [r*u, r*u*u+p, r*u*v, u*(E+p)])
    assert np.allclose(flux(U, 1), [r*v, r*u*v, r*v*v+p, v*(E+p)])
    assert abs(lam(U, 1) - (abs(v) + np.sqrt(g*p/r))) < 1e-12

def check_aligned_convexity_bound():
    # with the aligned orientation, the Monte Carlo update of aligned_flux_diagnostics.mc must equal the convex
    # combination of eq. (convex): U_i + sum 2|c| s (Ubar - U_i)/S, i.e. never leave the admissible set; the worst
    # min(rho,p) must be positive for all degrees and both jitters
    import aligned_flux_diagnostics as af
    for jit in (0.0, 0.2):
        P, L = sd.make_cloud(12, jit, 42); idx, off, m = sd.neighbour_table(P, L, 2.5)
        for q in (1, 3):
            c = sd.derivative_weights(off, m, 2.5, q, True)
            b, t, w = af.mc(c, off, m, P, 'aligned', trials=2000, seed=7)
            print(f"aligned, jitter {jit}, q={q}: {b}/{t} inadmissible, worst {w:.3g}")
            assert b == 0

if __name__ == "__main__":
    check_exponents(); check_neighbour_symmetry(); check_flux_helpers()
    check_polynomial_exactness(); check_aligned_convexity_bound()
    print("all stencil checks passed")

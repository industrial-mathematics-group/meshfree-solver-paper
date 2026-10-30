"""Monte Carlo check of the first-order fallback: piecewise constant states, Rusanov flux with the code's orientation,
the MLS derivative weights of degree 1 and 3 on a perturbed lattice, random admissible Euler states, time step at the
limit of condition (5.5). Run: python3 fallback_positivity.py"""
# First-order fallback (piecewise constant states, Rusanov, code's orientation) with the actual MLS derivative weights
# of degree 1 and degree 3 of a perturbed lattice; random admissible data; time step at the limit of (5.5).
import sys, numpy as np
import os; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stencil_diagnostics as sd
g = 1.4
def flux(U, d):
    r, mx, my, E = U; u, v = mx/r, my/r; p = (g-1)*(E-0.5*r*(u*u+v*v)); vel = (u, v)[d]
    return np.array([r*vel, mx*vel + (p if d == 0 else 0), my*vel + (p if d == 1 else 0), vel*(E+p)])
def lam(U, d):
    r, mx, my, E = U; u, v = mx/r, my/r; p = (g-1)*(E-0.5*r*(u*u+v*v)); return abs((u, v)[d]) + np.sqrt(g*p/r)
def cons(r, u, v, p): return np.array([r, r*u, r*v, p/(g-1)+0.5*r*(u*u+v*v)])
def pres(U): r, mx, my, E = U; return (g-1)*(E-0.5*(mx*mx+my*my)/r)
P, L = sd.make_cloud(48, 0.2, 42)
idx, off, m = sd.neighbour_table(P, L, 2.5)
rng = np.random.default_rng(1)
for q in (1, 3):
    c = sd.derivative_weights(off, m, 2.5, q, True)
    bad = 0; trials = 20000; worst = np.inf
    for t in range(trials):
        i = rng.integers(len(P)); ks = np.where(m[i])[0]
        Ui = cons(rng.uniform(0.1, 3), rng.normal()*3, rng.normal()*3, rng.uniform(1e-4, 0.05))
        Uj = {k: cons(rng.uniform(0.1, 3), rng.normal()*3, rng.normal()*3, rng.uniform(1e-4, 0.05)) for k in ks}
        rhs = np.zeros(4); S = 0.0
        for k in ks:
            for d in range(2):
                UL, UR = (Ui, Uj[k]) if off[i, k, d] > 0 else (Uj[k], Ui)
                s = max(lam(UL, d), lam(UR, d))
                Fn = 0.5*(flux(UL, d) + flux(UR, d) - s*(UR - UL))
                rhs += -2*c[i, k, d]*(Fn - flux(Ui, d)); S += s*abs(c[i, k, d])
        Unew = Ui + rhs/S
        mval = min(Unew[0], pres(Unew)); worst = min(worst, mval); bad += mval <= 0
    print(f"degree {q}: {bad} of {trials} random first-order updates at the limit of (5.5) are inadmissible (min of rho, p: {worst:.3g})")

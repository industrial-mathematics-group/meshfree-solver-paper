"""Aligned dissipation (paper, Secs. "Interface fluxes" and "Positivity"): (1) Monte Carlo check of the first-order
fallback with the Rusanov flux oriented by sign(c_ij^(d)) (aligned) and by sign(x_ij^(d)) (geometric), degree-1 and
degree-3 weights of the perturbed 48x48 lattice (kappa = 2.5), random admissible Euler states, time step at the limit
of the positivity CFL condition (eq:cflpos); this gives the "about 9 %" of the paper; (2) share of pairs and directions
on which the two orientations of the aligned flux disagree, sign(c_ij^(d)) = sign(c_ji^(d)) (the flux is then not
symmetric) on the 48x48 clouds; stencil_diagnostics.py prints the same share for the 300x300 cloud of the table.
Run: python3 aligned_flux_diagnostics.py"""
import sys, os, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stencil_diagnostics as sd
from fallback_positivity_lib import flux, lam, cons, pres
def mc(c, off, m, P, orient, trials=20000, seed=1):
    rng = np.random.default_rng(seed); bad = 0; worst = np.inf
    for t in range(trials):
        i = rng.integers(len(P)); ks = np.where(m[i])[0]
        Ui = cons(rng.uniform(0.1, 3), rng.normal()*3, rng.normal()*3, rng.uniform(1e-4, 0.05))
        Uj = {k: cons(rng.uniform(0.1, 3), rng.normal()*3, rng.normal()*3, rng.uniform(1e-4, 0.05)) for k in ks}
        rhs = np.zeros(4); S = 0.0
        for k in ks:
            for d in range(2):
                o = off[i, k, d] if orient == 'geometric' else c[i, k, d]
                UL, UR = (Ui, Uj[k]) if o > 0 else (Uj[k], Ui)
                s = max(lam(UL, d), lam(UR, d))
                Fn = 0.5*(flux(UL, d) + flux(UR, d) - s*(UR - UL))
                rhs += -2*c[i, k, d]*(Fn - flux(Ui, d)); S += s*abs(c[i, k, d])
        Unew = Ui + rhs/S
        mval = min(Unew[0], pres(Unew)); worst = min(worst, mval); bad += mval <= 0
    return bad, trials, worst
sign_mismatch = sd.sign_mismatch
if __name__ == "__main__":
     for jit in (0.0, 0.2):
        P, L = sd.make_cloud(48, jit, 42); idx, off, m = sd.neighbour_table(P, L, 2.5)
        for q in (1, 3):
            c = sd.derivative_weights(off, m, 2.5, q, True)
            sh, wsh = sign_mismatch(idx, m, c)
            line = f"jitter {jit}, degree {q}: pairs x directions with sign(c_ij)=sign(c_ji): {100*sh:.2f}% (weight share {100*wsh:.2f}%)"
            if jit > 0:
                for orient in ('geometric', 'aligned'):
                    b, t, w = mc(c, off, m, P, orient)
                    line += f"\n   {orient:9s}: {b} of {t} first-order updates inadmissible (min of rho, p: {w:.3g})"
            print(line, flush=True)

"""Monte Carlo check of the first-order fallback with the geometric orientation of the Rusanov flux: piecewise constant
states, the MLS derivative weights of degree 1 and 3 on the perturbed 48x48 lattice, random admissible Euler states,
time step at the limit of the positivity CFL condition (eq:cflpos of the paper). It runs the same experiment as
aligned_flux_diagnostics.py (same function, same seeds), restricted to the geometric orientation.
Run: python3 fallback_positivity.py"""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stencil_diagnostics as sd
from aligned_flux_diagnostics import mc

P, L = sd.make_cloud(48, 0.2, 42)
idx, off, m = sd.neighbour_table(P, L, 2.5)
for q in (1, 3):
    c = sd.derivative_weights(off, m, 2.5, q, True)
    bad, trials, worst = mc(c, off, m, P, 'geometric')
    print(f"degree {q}: {bad} of {trials} first-order updates inadmissible ({100*bad/trials:.1f}%), min of rho, p: {worst:.3g}")

"""Margin of the CFL time step against the positivity condition of the first-order fallback.

The time step uses the weights c-hat (fit without constant term); the positivity condition uses the weights c
of the fit with constant term. Prints rho = max over particles k, neighbours l in cbar(k) and directions d of
sum_j |c_kj^(d)| / sum_j |c-hat_lj^(d)| (the time step satisfies the condition at U^n if rho * CFL <= C),
for degree-one and degree-three weights, on a 200 x 200 periodic lattice perturbed by 0.2 h.
Run:  python3 cfl_positivity_margin.py
"""
import os
import sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stencil_diagnostics as sd
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "fallback_convergence.py")).read().split("def run")[0].split("from scipy")[1].split("\n",1)[1])
for kappa, qs in ((2.5,(1,3)),(5.5,(1,3))):
    P, L = cloud(200, 2, 0.2, seed=3)
    idx, off, m = sd.neighbour_table(P, L, kappa)
    W = {q:(np.abs(sd.derivative_weights(off,m,kappa,q,True)).sum(1), np.abs(sd.derivative_weights(off,m,kappa,q,False)).sum(1)) for q in qs}
    J = np.where(m, idx, 0)
    for qc in qs:
      for qh in qs:
        if qc>qh: continue
        B, A = W[qc][0], W[qh][1]
        own = (B/A).max()
        nbr = np.max(np.where(m[...,None], B[:,None,:]/A[J], 0).max(1))
        rho = max(own, nbr)
        print(f"kappa={kappa} c deg {qc} vs chat deg {qh}: max own ratio {own:.3f}, rho (over neighbours) {rho:.3f}, mean l1 rel diff same particle {np.mean(np.abs(W[qc][0]/W[qc][1]-1)):.4f}")

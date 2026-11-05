"""Brute-force check of Obs. lattice (i): 2-D lattice, K = 4, kappa = 3.5, geometric orientation.  Eigenvalues of the
assembled periodic operator (n x n lattice) vs the symbol maximum claimed in the paper (7.7e-5 for a=(1,0.5), 2.2e-3 for
a=(1,0)); the aligned orientation must have max Re <= round-off."""
import os, sys, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
import linop
for a in ([1.0, 0.5], [1.0, 0.0]):
    for orient in ("geometric", "aligned"):
        for n in (18, 30):
            P, h = linop.make_cloud(n, 2, 0.0)
            L = linop.build_operator(P, h, 3.5, 4, a, orient)
            ev = np.linalg.eigvals(L) * h
            k = np.argmax(ev.real)
            print(f"a={a} {orient} n={n}: max Re(lambda) h / max|a| = {ev.real[k] / max(abs(x) for x in a):.2e}  (Im h = {ev.imag[k]:.3f})")

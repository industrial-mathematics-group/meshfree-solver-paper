"""Bloch symbols use 3 copies of the supercell; the operator couples particles up to 2R = 2*kappa*h apart, so for a
supercell of width m*h < 2R couplings to the block two cells away alias onto the neighbouring block and get the
wrong phase. Compare copies=3 with copies=5 (correct for reach up to 2 cells)."""
import sys
sys.path.insert(0, sys.argv[1])
import numpy as np
import ho_common as hc

def bloch(P0, K, a, th, copies, mfix=None):
    return hc.bloch_symbols(P0, 2.5, K, a, "geometric", th, copies=copies)

D = 2
for m, label in ((4, "jittered seed 1000"), (6, "jittered seed 1000")):
    rng = np.random.default_rng(1000)
    g = (np.arange(m) + 0.5) / m
    P0 = np.stack(np.meshgrid(g, g, indexing="ij"), axis=-1).reshape(-1, 2)
    P0 = np.mod(P0 + 0.2 / m * (2 * rng.random(P0.shape) - 1), 1.0)
    t1 = np.linspace(-np.pi, np.pi, 8, endpoint=False)
    th = np.array([(x, y) for x in t1 for y in t1])
    for K in (2, 3):
        s3, h3 = bloch(P0, K, [1.0, 0.5], th, 3)
        s5, h5 = bloch(P0, K, [1.0, 0.5], th, 5)
        # symbols are in units of the tiled torus; scale by h to compare
        d = max(np.abs(x * h3 - y * h5).max() for x, y in zip(s3, s5))
        a3 = max(np.linalg.eigvals(S).real.max() for S in s3) * h3
        a5 = max(np.linalg.eigvals(S).real.max() for S in s5) * h5
        print(f"2-D m={m} K={K}: max|h*S(copies=3) - h*S(copies=5)| = {d:.2e}; alpha_h copies=3: {a3:.3e}, copies=5: {a5:.3e}")

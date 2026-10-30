"""Von Neumann symbols of the scheme on affine lattices A Z^D (frozen operators of a smoothly deformed lattice).

For a diagonal A = diag(a_1, ..., a_D) (separable deformations) the stencil of the central particle of a large patch
is read off and the symbol mu(theta) = sum_l beta_l exp(i theta . l) is evaluated on a grid of theta.
Reports max_theta Re mu (h = 1 units) and the neighbour set size; the hypothesis (S) of the deformed-lattice theorem
is max Re mu <= 0 for all A in the range of Dphi.
Usage: python3 ho_frozen.py D kappa K1,K2,... amin amax na ntheta out.md [geometric,aligned]
"""
import itertools
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import build_operator, neighbours  # noqa: E402

D, kappa = int(sys.argv[1]), float(sys.argv[2])
Ks = [int(x) for x in sys.argv[3].split(",")]
amin, amax, na, ntheta, out = float(sys.argv[4]), float(sys.argv[5]), int(sys.argv[6]), int(sys.argv[7]), sys.argv[8]
orients = sys.argv[9].split(",") if len(sys.argv) > 9 else ["geometric"]
a = [1.0] if D == 1 else [1.0, 0.5]
M = int(2 * kappa) + 3                     # patch half-width in lattice steps (two stencil layers fit)
n = 2 * M + 1
h = 1.0 / (4 * n)                          # small spacing so that the patch is far from the torus wrap
lines = ["| D | kappa | K | orient | A | #nb | max_theta Re mu | theta_worst |", "|---|---|---|---|---|---|---|---|"]
grid = np.arange(-M, M + 1)
idx = np.array(list(itertools.product(grid, repeat=D)))
centre = int(np.where((idx == 0).all(1))[0][0])
th1 = np.linspace(-np.pi, np.pi, ntheta, endpoint=False)
thetas = np.array(list(itertools.product(th1, repeat=D)))
avals = np.linspace(amin, amax, na)
for A in (avals if D == 1 else itertools.product(avals, repeat=D)):
    Avec = np.atleast_1d(np.array(A, float))
    P = 0.5 + idx * Avec * h                 # affine lattice around the torus centre
    nb = neighbours(P, kappa * h)
    for K in Ks:
        for orient in orients:
            L = build_operator(P, h, kappa, K, a, orient, nb=nb)
            row = L[centre] * h              # dimensionless stencil beta_l
            sym = row @ np.exp(1j * (idx @ thetas.T))
            i = int(np.argmax(sym.real))
            line = "| %d | %g | %d | %s | %s | %d | %.3e | %s |" % (
                D, kappa, K, orient, np.round(Avec, 3).tolist(), len(nb[centre][0]), sym.real[i],
                np.round(thetas[i], 3).tolist())
            print(line, flush=True)
            lines.append(line)
with open(out, "w") as f:
    f.write("\n".join(lines) + "\n")

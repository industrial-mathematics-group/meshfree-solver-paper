"""The left null vector pi of the high-order operator (pi^T L = 0) as a candidate weight for an energy estimate.

For K = 1 the stationary distribution pi is positive, and L is contractive in l2(pi) (stability note, Thm 4.1).
For K >= 2 this script computes pi, checks positivity, the spread rho = max(pi/V)/min(pi/V), the numerical abscissa
omega_pi = max eig of (Pi L + L^T Pi)/2 w.r.t. Pi (times h), and the conservation defect density d = V^{-1} L^T V
of the volume norm (times h, rms and max), which drives the lower bound on the numerical abscissa in the V norm.
Usage: python3 ho_pi.py D kappa jitter n1,n2,... K1,K2,... nseeds out.md [geometric,aligned]
"""
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import sym_abscissa, volumes  # noqa: E402
from linop import build_operator, first_order_operator, make_cloud, neighbours  # noqa: E402

D, kappa, jit = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ns = [int(x) for x in sys.argv[4].split(",")]
Ks = [int(x) for x in sys.argv[5].split(",")]
nseeds, out = int(sys.argv[6]), sys.argv[7]
orients = sys.argv[8].split(",") if len(sys.argv) > 8 else ["geometric"]
a = [1.0] if D == 1 else [1.0, 0.5]
lines = ["| D | kappa | jitter | n | seed | K | orient | min(pi)/max(pi) | rho(pi/V) | omega_V*h | omega_pi*h | rms(d)*h | max(d)*h | lower bound*h |",
         "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
for n in ns:
    for seed in range(nseeds):
        P, h = make_cloud(n, D, jit, seed)
        nb = neighbours(P, kappa * h)
        V = volumes(P, h)
        for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
            L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else build_operator(P, h, kappa, K, a, orient, nb=nb)
            # left null vector: smallest singular vector of L^T
            u, s, vt = sl.svd(L.T)
            pi = vt[-1]
            pi = pi / pi.sum()
            ratio = pi.min() / pi.max()
            d = (L.T @ V) / V
            rms, mx = np.sqrt(np.mean(d ** 2)), np.abs(d).max()
            omV = sym_abscissa(L, V)
            normL = np.linalg.norm(np.diag(np.sqrt(V)) @ L @ np.diag(1 / np.sqrt(V)), 2)
            lb = np.sum(V * d ** 2) / (9 * normL)   # constant 9 of prop:obstruction (fixed 2026-11-04: was 16)
            if ratio > 0:
                rho = (pi / V).max() / (pi / V).min()
                omp = sym_abscissa(L, pi)
                line = "| %d | %g | %g | %d | %d | %d | %s | %.3f | %.2f | %.2e | %.2e | %.2e | %.2e | %.1e |" % (
                    D, kappa, jit, n, seed, K, orient, ratio, rho, omV * h, omp * h, rms * h, mx * h, lb * h)
            else:
                line = "| %d | %g | %g | %d | %d | %d | %s | %.3f (not positive) | -- | %.2e | -- | %.2e | %.2e | %.1e |" % (
                    D, kappa, jit, n, seed, K, orient, ratio, omV * h, rms * h, mx * h, lb * h)
            print(line, flush=True)
            lines.append(line)
with open(out, "w") as f:
    f.write("\n".join(lines) + "\n")

"""Local symbols of the high-order operator on jittered clouds: the parity dichotomy.

lambda_i(theta) = sum_j L_ij exp(i theta x_ij / h) is the local symbol at particle i. Since L reproduces polynomials of
degree <= K-1, Re lambda_i(theta) = (-1)^k sum_j L_ij (theta x_ij/h)^{2k}/(2k)! + O(theta^{2k+2}/h) with 2k the smallest
even integer >= K. For K = 2 in 1-D this is -theta^2 D_i / h with the local diffusion coefficient
   D_i = (h/2) sum_j L_ij (x_ij/h)^2   (dimensionless; zero on lattices),
whose cloud average Dbar decides whether smooth modes are damped (Dbar > 0) or amplified (Dbar < 0); for K = 3 the
analogous coefficient of theta^4 is compared with the lattice value. The script prints the mean, the standard deviation
and the predicted maximal growth rate alpha h = Dbar^2/(4 c4) for Dbar < 0 (c4: cloud-average fourth-order coefficient).
Usage: python3 ho_local_symbol.py kappa jitter n1,n2,... nseeds out.md
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import volumes  # noqa: E402
from linop import build_operator, make_cloud, neighbours  # noqa: E402

kappa, jit = float(sys.argv[1]), float(sys.argv[2])
ns = [int(x) for x in sys.argv[3].split(",")]
nseeds, out = int(sys.argv[4]), sys.argv[5]
lines = ["| kappa | jitter | n | seed | K | nb range | mean D2 | std D2 | mean D4 | std D4 | predicted alpha*h | measured alpha*h |",
         "|---|---|---|---|---|---|---|---|---|---|---|---|"]
for n in ns:
    for seed in range(nseeds):
        P, h = make_cloud(n, 1, jit, seed)
        nb = neighbours(P, kappa * h)
        V = volumes(P, h)
        x = P[:, 0]
        for K in (2, 3):
            L = build_operator(P, h, kappa, K, [1.0], "geometric", nb=nb)
            X = x[None, :] - x[:, None]
            X -= np.round(X)
            Y = X / h
            D2 = 0.5 * h * (L * Y ** 2).sum(1)                 # coefficient of -theta^2 / h in Re lambda_i
            D4 = -h * (L * Y ** 4).sum(1) / 24.0                # coefficient of -theta^4 / h  (cos expansion: +theta^4/24)
            m2, s2 = np.sum(V * D2) / V.sum(), np.sqrt(np.sum(V * (D2 - np.sum(V * D2) / V.sum()) ** 2) / V.sum())
            m4, s4 = np.sum(V * D4) / V.sum(), np.sqrt(np.sum(V * (D4 - np.sum(V * D4) / V.sum()) ** 2) / V.sum())
            pred = (m2 ** 2 / (4 * m4)) if (m2 < 0 and m4 > 0) else 0.0
            alpha = np.linalg.eigvals(L).real.max() * h
            cnt = sorted(set(len(j) for j, _ in nb))
            line = "| %g | %g | %d | %d | %d | %s | %.2e | %.2e | %.3e | %.2e | %.1e | %.1e |" % (
                kappa, jit, n, seed, K, cnt, m2, s2, m4, s4, pred, alpha)
            print(line, flush=True)
            lines.append(line)
with open(out, "w") as f:
    f.write("\n".join(lines) + "\n")

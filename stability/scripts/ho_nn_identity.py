"""Order two in one dimension with nearest-neighbour stencils (one neighbour on each side): the exact energy identity.

With dual volumes V_i = (x_{i+1} - x_{i-1})/2 the scheme is the finite-volume MUSCL scheme on the dual cells and
   d/dt ||U||_V^2 = -a Q(sigma),   Q = sum_i m_i sigma_i (sigma_i - sigma_{i-1}),
   sigma_i = (U_{i+1} - U_i)/g_i (slope on gap i),  m_i = w_- g_{i-1}^2 g_i^2 / (w_+ g_i^2 + w_- g_{i-1}^2),
   = 1/2 sum_i m_i (sigma_i - sigma_{i-1})^2 + 1/2 sum_i (m_i - m_{i+1}) sigma_i^2.
The script checks the identity against the assembled operator, and reports for the smoothest mode U = cos(2 pi x)
the two parts of Q, the Rayleigh quotient, the numerical abscissa in the dual-volume norm, and the spectral abscissa.
Usage: python3 ho_nn_identity.py kappa jitter n1,n2,... nseeds out.md
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import sym_abscissa, volumes  # noqa: E402
from linop import build_operator, make_cloud, neighbours, weight  # noqa: E402

kappa, jit = float(sys.argv[1]), float(sys.argv[2])
ns = [int(x) for x in sys.argv[3].split(",")]
nseeds, out = int(sys.argv[4]), sys.argv[5]
lines = ["| n | seed | nb | identity err | Q4 (smooth) | Qtel (smooth) | Rayleigh*h (smooth) | omega_dual*h | alpha*h | #Re lambda>1e-10 |",
         "|---|---|---|---|---|---|---|---|---|---|"]
for n in ns:
    for seed in range(nseeds):
        P, h = make_cloud(n, 1, jit, seed)
        nb = neighbours(P, kappa * h)
        cnt = sorted(set(len(j) for j, _ in nb))
        L = build_operator(P, h, kappa, 2, [1.0], "geometric", nb=nb)
        order = np.argsort(P[:, 0])
        x = P[order, 0]
        g = np.diff(np.concatenate([x, [x[0] + 1.0]]))            # g_i between sorted i and i+1
        V = volumes(P, h)[order]
        R = kappa * h
        wp = weight(g ** 2, R)                                      # weight of the right neighbour of i
        wm = weight(np.roll(g, 1) ** 2, R)                          # weight of the left neighbour of i
        gm = np.roll(g, 1)
        mcoef = wm * gm ** 2 * g ** 2 / (wp * g ** 2 + wm * gm ** 2)
        Ls = L[np.ix_(order, order)]
        rng = np.random.default_rng(seed)
        U = rng.standard_normal(n)
        sig = (np.roll(U, -1) - U) / g
        Q = np.sum(mcoef * sig * (sig - np.roll(sig, 1)))
        lhs = 2 * np.sum(V * U * (Ls @ U))
        err = abs(lhs + Q) / abs(Q)
        Us = np.cos(2 * np.pi * x)
        sig = (np.roll(Us, -1) - Us) / g
        Q4 = 0.5 * np.sum(mcoef * (sig - np.roll(sig, 1)) ** 2)
        Qt = 0.5 * np.sum((mcoef - np.roll(mcoef, -1)) * sig ** 2)
        ray = np.sum(V * Us * (Ls @ Us)) / np.sum(V * Us ** 2)
        om = sym_abscissa(Ls, V)
        ev = np.linalg.eigvals(Ls)
        line = "| %d | %d | %s | %.1e | %.3e | %.3e | %.3e | %.3e | %.2e | %d |" % (
            n, seed, cnt, err, Q4, Qt, ray * h, om * h, ev.real.max() * h, int((ev.real > 1e-10).sum()))
        print(line, flush=True)
        lines.append(line)
with open(out, "w") as f:
    f.write("\n".join(lines) + "\n")

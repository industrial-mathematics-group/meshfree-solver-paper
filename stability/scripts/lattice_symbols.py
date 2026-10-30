"""Von Neumann analysis of the linear scheme on Cartesian lattices.

The operator of linear advection on a periodic lattice is translation invariant, L U_i = sum_l beta_l U_{i+l};
its symbol lambda(theta) = sum_l beta_l exp(i theta . l) is evaluated on a fine grid of theta in [-pi, pi]^D.
Reports, for D = 1, 2, several kappa and K = 1..5 (no MOOD, no limiter, geometric orientation for K >= 2,
aligned first-order operator for K = 1; frozen = coupled here since all orders are K):
  * max_theta h*Re(lambda)/|a|  (semi-discrete von Neumann condition: <= 0),
  * the largest stable CFL number CFL_max of RK2 (Heun), RK3 (SSP) and SSPRK(5,4), in the normalisation of
    the implementation, Delta t = CFL / (D sum_d |a_d| sum_j |c_ij^(d)|), i.e. the largest CFL for which
    max_theta |R(Delta t lambda(theta))| <= 1 + 1e-12.
Output: rows of a Markdown table appended to the file given as last argument; columns
| D | kappa | a | K | q | orientation | max h Re lambda / max|a_d| | CFL_max RK2 | RK3 | SSPRK(5,4) |
"""
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import (build_operator, derivative_weights, first_order_operator, make_cloud,  # noqa: E402
                   neighbours, safeguarded_q)

SR54 = [  # Spiteri-Ruuth SSPRK(5,4), Shu-Osher form: (stage combos of previous u's, dt*L coefficients)
    ([1.0], [0.391752226571890]),
    ([0.444370493651235, 0.555629506348765], [0.0, 0.368410593050371]),
    ([0.620101851488403, 0.0, 0.379898148511597], [0.0, 0.0, 0.251891774271694]),
    ([0.178079954393132, 0.0, 0.0, 0.821920045606868], [0.0, 0.0, 0.0, 0.544974750228521]),
    ([0.0, 0.0, 0.517231671970585, 0.096059710526147, 0.386708617503269],
     [0.0, 0.0, 0.0, 0.063692468666290, 0.226007483236906]),
]


def R_rk(z, method):
    if method == "RK2":
        return 1 + z + z**2 / 2
    if method == "RK3":
        return 1 + z + z**2 / 2 + z**3 / 6
    u = [np.ones_like(z)]
    for al, be in SR54:
        u.append(sum(a * uk for a, uk in zip(al, u)) + sum(b * z * uk for b, uk in zip(be, u)))
    return u[-1]


def symbol(D, kappa, K, a, m=200, orient="geometric", s=None):
    n = int(np.ceil(4 * kappa)) + 4
    P, h = make_cloud(n, D, 0.0)
    nb = neighbours(P, kappa * h)
    L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else build_operator(P, h, kappa, K, a, orient, nb=nb, s=s)
    i0 = 0
    off = P - P[i0]
    off -= np.round(off)
    ints = np.round(off / h).astype(int)
    beta = L[i0] * h
    th1 = np.linspace(-np.pi, np.pi, m)
    TH = np.stack(np.meshgrid(*([th1] * D), indexing="ij"), axis=-1).reshape(-1, D)
    lam = (np.exp(1j * TH @ ints.T) * beta).sum(1)      # h * lambda
    js, offs = nb[i0]
    q = 1 if K == 1 else safeguarded_q(len(js), D, K)
    c = derivative_weights(offs, kappa * h, q, h) * h
    norm = D * sum(abs(a[d]) * np.abs(c[:, d]).sum() for d in range(D))  # h * D sum_d |a_d| sum_j |c|
    return lam, norm, q


def cfl_max(lam, norm, method):
    lo, hi = 0.0, 8.0
    for _ in range(60):
        mid = 0.5 * (lo + hi)
        if np.abs(R_rk(mid / norm * lam, method)).max() <= 1 + 1e-12:
            lo = mid
        else:
            hi = mid
    return lo


if __name__ == "__main__":
    # argv: D kappa1,kappa2 m out.md
    D = int(sys.argv[1])
    kappas = [float(x) for x in sys.argv[2].split(",")]
    m = int(sys.argv[3])
    out = sys.argv[4]
    vels = [[1.0]] if D == 1 else [[1.0, 0.5], [1.0, 0.0]]
    for kappa in kappas:
        for a in vels:
            for K in range(1, 6):
                for orient in (["aligned"] if K == 1 else ["geometric", "aligned"]):
                    try:
                        lam, norm, q = symbol(D, kappa, K, a, m, orient)
                    except np.linalg.LinAlgError:
                        continue
                    re = lam.real.max() / max(abs(x) for x in a)
                    cf = [cfl_max(lam, norm, meth) for meth in ("RK2", "RK3", "SR54")]
                    row = "| %d | %.1f | (%s) | %d | %d | %s | %.1e | %s | %s | %s |" % (
                        D, kappa, ", ".join("%g" % x for x in a), K, q, orient, re,
                        *["%.3f" % c if c < 7.99 else "> 8" for c in cf])
                    print(row, flush=True)
                    with open(out, "a") as f:
                        f.write(row + "\n")

"""Linear semi-discrete operator of the meshfree MUSCL scheme for scalar advection u_t + a.grad u = 0.

Independent NumPy re-implementation (not HyperCloud code) of the scheme of math_addendum.tex, Sec. 3-4:
  * reconstruction fit of degree k-1 in the Taylor basis without constant term, forced through U_i,
  * derivative weights c_ij of degree q (with constant term, neighbours only),
  * interface states at the pair midpoints, Rusanov flux with s_d = |a_d| per direction,
  * orientation sigma_ij,d = sign(x_ij,d) ("geometric", convention -1 for x_ij,d = 0) or sign(c_ij,d) ("aligned"),
  * L_i = -2 sum_j c_ij . (F*_ij - F(U_i)).
Periodic clouds: a jittered Cartesian lattice of spacing h = 1/n on the unit torus.
Weight w(r) = 1/(1 + y + y^2/2 + y^3/6 + y^4/24), y = r^2/R^2 (as in scripts/stencil_diagnostics.py).
Fits are unregularized (plain solves); the scaled variable x/h is used for conditioning.
"""
import itertools
from math import factorial

import numpy as np


def weight(r2, R):
    y = r2 / R**2
    return 1.0 / (1.0 + y * (1.0 + y * (0.5 + y * (1.0 / 6.0 + y / 24.0))))


def exponents(D, q):
    res = []
    for deg in range(1, q + 1):
        cur = [t for t in itertools.product(range(deg + 1), repeat=D) if sum(t) == deg]
        cur.sort(key=lambda t: (-max(t), tuple(reversed(t))))
        res += cur
    return res


def taylor(Y, exps):
    cols = []
    for a in exps:
        c = np.ones(Y.shape[:-1])
        for d, ad in enumerate(a):
            c = c * Y[..., d] ** ad / factorial(ad)
        cols.append(c)
    return np.stack(cols, axis=-1) if cols else np.zeros(Y.shape[:-1] + (0,))


def make_cloud(n, D, jitter, seed=0):
    rng = np.random.default_rng(seed)
    h = 1.0 / n
    g = (np.arange(n) + 0.5) * h
    P = np.stack(np.meshgrid(*([g] * D), indexing="ij"), axis=-1).reshape(-1, D)
    P = P + jitter * h * (2.0 * rng.random(P.shape) - 1.0)
    return np.mod(P, 1.0), h


def neighbours(P, R):
    """Lists of (j, offset x_j - x_i) on the unit torus, brute force."""
    N, D = P.shape
    nb = []
    for i in range(N):
        d = P - P[i]
        d -= np.round(d)
        r2 = (d**2).sum(1)
        js = np.where((r2 <= R**2 * (1 + 1e-12)) & (np.arange(N) != i))[0]
        nb.append((js, d[js]))
    return nb


def derivative_weights(off, R, q, h):
    """(K, D) weights c_ij^(d) of degree q with constant term."""
    D = off.shape[1]
    exps = exponents(D, q)
    Pm = np.concatenate([np.ones((len(off), 1)), taylor(off / h, exps)], axis=1)
    w = weight((off**2).sum(1), R)
    Nm = (Pm * w[:, None]).T @ Pm
    C = np.linalg.solve(Nm, (Pm * w[:, None]).T)     # (B+1, K)
    return C[1:1 + D].T / h


def recon_rows(off, R, r, h):
    """Matrix G (K, K): U_ij - U_i = sum_l G[j, l] (U_l - U_i), degree r fit at midpoint x_ij/2."""
    if r == 0:
        return np.zeros((len(off), len(off)))
    D = off.shape[1]
    exps = exponents(D, r)
    Pm = taylor(off / h, exps)
    w = weight((off**2).sum(1), R)
    Nm = (Pm * w[:, None]).T @ Pm
    A = np.linalg.solve(Nm, (Pm * w[:, None]).T)       # (B, K): coefficients per data slot
    return taylor(0.5 * off / h, exps) @ A              # (K, K)


def qdiv(k):
    return 2 * ((k + 1) // 2) - 1


def nbasis(D, q):
    return len(exponents(D, q))


def safeguarded_q(nnb, D, K):
    """Divergence degree with the safeguards of Remark 3.7 (rem:safeguards)."""
    q = qdiv(K)
    if q > K - 1 and not (nnb >= 1.5 * (nbasis(D, K) + 1) and (D < 3 or q <= 3)):
        q = max(K - 1, 1)
    while q > 1 and nnb < nbasis(D, q) + 1:
        q -= 1
    return q


def build_operator(P, h, kappa, K, a, orient="geometric", q=None, nb=None, s=None):
    """Dense N x N matrix of the linear operator L for order K (no MOOD, no limiter).

    s: dissipation speeds per direction (default |a_d|, the Rusanov speed of linear advection).
    """
    N, D = P.shape
    R = kappa * h
    a = np.asarray(a, float)
    spd = np.abs(a) if s is None else np.asarray(s, float)
    if nb is None:
        nb = neighbours(P, R)
    # interface-state maps: Ustate[i][jslot] = row vector over global indices
    G = []
    C = []
    for i in range(N):
        js, off = nb[i]
        G.append(recon_rows(off, R, K - 1, h))
        C.append(derivative_weights(off, R, safeguarded_q(len(js), D, K) if q is None else q, h))
    slot = [dict((j, s) for s, j in enumerate(nb[i][0])) for i in range(N)]
    L = np.zeros((N, N))
    for i in range(N):
        js, off = nb[i]
        c = C[i]
        for s, j in enumerate(js):
            # U_ij = U_i + sum_l G_i[s,l](U_l - U_i)
            Uij = np.zeros(N)
            Uij[i] += 1.0 - G[i][s].sum()
            np.add.at(Uij, js, G[i][s])
            t = slot[j][i]
            jl, _ = nb[j]
            Uji = np.zeros(N)
            Uji[j] += 1.0 - G[j][t].sum()
            np.add.at(Uji, jl, G[j][t])
            for d in range(D):
                if orient == "geometric":
                    sg = np.sign(off[s, d]) if off[s, d] != 0 else -1.0
                else:
                    sg = np.sign(c[s, d])
                Fs = 0.5 * a[d] * (Uij + Uji) - 0.5 * spd[d] * sg * (Uji - Uij)
                Fs[i] -= a[d]
                L[i] -= 2.0 * c[s, d] * Fs
    return L


def first_order_operator(P, h, kappa, a, q=1, nb=None):
    """First-order aligned operator (K = 1): piecewise constant states, aligned orientation."""
    N, D = P.shape
    R = kappa * h
    a = np.asarray(a, float)
    if nb is None:
        nb = neighbours(P, R)
    L = np.zeros((N, N))
    for i in range(N):
        js, off = nb[i]
        c = derivative_weights(off, R, q, h)
        for s, j in enumerate(js):
            for d in range(D):
                coef = abs(a[d]) * abs(c[s, d]) - a[d] * c[s, d]
                L[i, j] += coef
                L[i, i] -= coef
    return L

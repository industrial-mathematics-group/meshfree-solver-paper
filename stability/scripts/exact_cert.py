# From the independent review of 3 Nov 2026 (reviews/meshfree-solver-paper/stability/), added 4 Nov 2026.
"""Exact (rational) a posteriori check of 1-D defect certificates of ho_defect_cert.py.

1. Rebuild the single-defect operator L of ho_defect_cert.operator in exact rational arithmetic (positions, weights,
   fits are rational in 1-D), compare with the float64 operator.
2. Solve the certificate SDP as the script does (float), rationalise W_Z and the Fejer-Riesz factor b exactly
   (their binary values), form E(W) exactly and test  t I - E|_{Z'} > 0  by an exact LDL^T for t slightly above the
   float residual, and  W_Z - c_W g I > 0.  Also report the largest entry of E outside Z' x Z' (exactly), which
   is nonzero only because b is a floating-point factor.
Usage: python exact_cert.py <stability/scripts> type K g rho
"""
import sys
from fractions import Fraction as F
from math import factorial
import numpy as np
sys.path.insert(0, sys.argv[1])
import ho_defect_cert as hdc
from linop import qdiv, nbasis

KAPPA = F(5, 2)

def weight(r2, R2):
    y = r2 / R2
    return 1 / (1 + y * (1 + y * (F(1, 2) + y * (F(1, 6) + y / 24))))

def solve(A, B):
    """exact Gauss-Jordan: A (n x n) list of lists, B (n x k)."""
    n = len(A); k = len(B[0])
    M = [list(A[i]) + list(B[i]) for i in range(n)]
    for c in range(n):
        p = next(r for r in range(c, n) if M[r][c] != 0)
        M[c], M[p] = M[p], M[c]
        piv = M[c][c]
        M[c] = [v / piv for v in M[c]]
        for r in range(n):
            if r != c and M[r][c] != 0:
                f = M[r][c]
                M[r] = [a - f * b for a, b in zip(M[r], M[c])]
    return [row[n:] for row in M]

def safeguarded_q(nnb, K):
    q = qdiv(K)
    if q > K - 1 and not (nnb >= 1.5 * (nbasis(1, K) + 1)):
        q = max(K - 1, 1)
    while q > 1 and nnb < nbasis(1, q) + 1:
        q -= 1
    return q

def exact_operator(xs, period, K, orient):
    """xs: list of Fractions on [0, period); units h = 1 (as ho_defect_cert.operator)."""
    N = len(xs); R2 = KAPPA ** 2
    nb = []
    for i in range(N):
        js, off = [], []
        for j in range(N):
            if j == i: continue
            d = xs[j] - xs[i]
            d -= period * round(d / period)
            if d * d <= R2:
                js.append(j); off.append(d)
        nb.append((js, off))
    G, C = [], []
    for i in range(N):
        js, off = nb[i]
        w = [weight(d * d, R2) for d in off]
        q = safeguarded_q(len(js), K)
        # derivative weights: basis [1, y, y^2/2, ...], degree q, row 1 = d/dy
        P = [[F(1)] + [d ** a / factorial(a) for a in range(1, q + 1)] for d in off]
        Nm = [[sum(w[s] * P[s][a] * P[s][b] for s in range(len(off))) for b in range(q + 1)] for a in range(q + 1)]
        rhs = [[w[s] * P[s][a] for s in range(len(off))] for a in range(q + 1)]
        Cm = solve(Nm, rhs)
        C.append(Cm[1])
        r = K - 1
        if r == 0:
            G.append([[F(0)] * len(off) for _ in off]); continue
        T = [[d ** a / factorial(a) for a in range(1, r + 1)] for d in off]
        Nm = [[sum(w[s] * T[s][a] * T[s][b] for s in range(len(off))) for b in range(r)] for a in range(r)]
        rhs = [[w[s] * T[s][a] for s in range(len(off))] for a in range(r)]
        A = solve(Nm, rhs)
        Tm = [[(d / 2) ** a / factorial(a) for a in range(1, r + 1)] for d in off]
        G.append([[sum(Tm[s][a] * A[a][l] for a in range(r)) for l in range(len(off))] for s in range(len(off))])
    slot = [{j: s for s, j in enumerate(nb[i][0])} for i in range(N)]
    L = [[F(0)] * N for _ in range(N)]
    for i in range(N):
        js, off = nb[i]
        for s, j in enumerate(js):
            Uij = {i: 1 - sum(G[i][s])}
            for l, jl in enumerate(js): Uij[jl] = Uij.get(jl, 0) + G[i][s][l]
            t = slot[j][i]; jl_, _ = nb[j]
            Uji = {j: 1 - sum(G[j][t])}
            for l, jj in enumerate(jl_): Uji[jj] = Uji.get(jj, 0) + G[j][t][l]
            if orient == "geometric":
                sg = 1 if off[s] > 0 else -1
            else:
                sg = (C[i][s] > 0) - (C[i][s] < 0)
            c = C[i][s]
            keys = set(Uij) | set(Uji)
            for k in keys:
                a_, b_ = Uij.get(k, 0), Uji.get(k, 0)
                Fs = F(1, 2) * (a_ + b_) - F(1, 2) * sg * (b_ - a_)
                L[i][k] -= 2 * c * Fs
            L[i][i] -= 2 * c * (-1)
    return L

def ldl_pd(M):
    """exact test: M symmetric (Fractions) positive definite?  returns (bool, min pivot)."""
    n = len(M); A = [row[:] for row in M]; mins = None
    for k in range(n):
        p = A[k][k]
        if p <= 0: return False, p
        mins = p if mins is None or p < mins else mins
        for i in range(k + 1, n):
            if A[i][k] != 0:
                f = A[i][k] / p
                for j in range(k + 1, n):
                    A[i][j] -= f * A[k][j]
    return True, mins

if __name__ == "__main__":
    typ, K, g, rho = sys.argv[2], int(sys.argv[3]), float(sys.argv[4]), int(sys.argv[5])
    rec, WZ, _ = hdc.certificate(typ, K, "geometric", g, rho)
    print("float certificate:", {k: rec[k] for k in ("t", "wmin", "wmax", "status", "nz", "nzp")})
    n = 64
    x, z = hdc.defect_sites(n, g, typ, n // 2)
    period = n * g
    Lf = hdc.operator(x, period, K, "geometric")
    gF = F(g); xs = [F(v) for v in x]; perF = F(period)
    # use exact float values of x (binary), period as float value
    L = exact_operator(xs, perF, K, "geometric")
    N = len(xs)
    Le = np.array([[float(v) for v in row] for row in L])
    print("max |L_exact - L_float| =", np.abs(Le - Lf).max(), " max|L| =", np.abs(Lf).max())
    b, d, m, err = hdc.local_squares_1d(K, "geometric", hdc.KAPPA, g)
    Bsum, dist = hdc.far_squares(x, period, b, g, [z], rho)
    Z = np.where(dist <= rho * g + 1e-9)[0]
    # far squares exactly
    bF = [F(v) for v in b]
    pos = {round(v, 6): i for i, v in enumerate(x)}
    B = [[F(0)] * N for _ in range(N)]
    for i in range(N):
        idx = [pos.get(round((x[i] + k * g) % period, 6)) for k in range(len(b))]
        if any(j is None or dist[j] <= rho * g + 1e-9 for j in idx): continue
        for a_, ia in enumerate(idx):
            for c_, ic in enumerate(idx):
                B[ia][ic] += bF[a_] * bF[c_]
    W = [[F(0)] * N for _ in range(N)]
    for i in range(N): W[i][i] = gF
    Zs = list(Z)
    for a_, ia in enumerate(Zs):
        W[ia][ia] = F(0)
    for a_, ia in enumerate(Zs):
        for c_, ic in enumerate(Zs):
            W[ia][ic] = F(float(0.5 * (WZ[a_, c_] + WZ[c_, a_])))
    # E = W L + L^T W + B  (W banded-ish: dense block on Z, diagonal elsewhere)
    nzW = [[(k, W[i][k]) for k in range(N) if W[i][k] != 0] for i in range(N)]
    WL = [[sum(wv * L[k][j] for k, wv in nzW[i]) for j in range(N)] for i in range(N)]
    E = [[WL[i][j] + WL[j][i] + B[i][j] for j in range(N)] for i in range(N)]
    touch = set(Zs)
    for i in Zs:
        touch |= set(np.where(np.abs(Lf[i]) > 1e-14)[0]) | set(np.where(np.abs(Lf[:, i]) > 1e-14)[0])
    Zp = sorted(touch)
    out = max((abs(E[i][j]) for i in range(N) for j in range(N) if not (i in touch and j in touch)), default=0)
    print("|Z| =", len(Zs), " |Z'| =", len(Zp), " max |E_exact| outside Z'xZ' =", float(out))
    Ez = [[E[i][j] for j in Zp] for i in Zp]
    import mpmath as mp
    mp.mp.dps = 50
    ev = mp.eigsy(mp.matrix([[mp.mpf(v.numerator) / v.denominator for v in row] for row in Ez]))[0]
    lmax = max(ev)
    print("lambda_max(E_exact|Z') (50 digits) =", mp.nstr(lmax, 12), "  float a posteriori t =", rec["t"])
    for fac in (1 + 1e-6, 1 + 1e-3):
        tt = F(float(lmax) * fac) if float(lmax) > 0 else F(1, 10**14)
        ok, mp_ = ldl_pd([[(tt if i == j else 0) - Ez[i][j] for j in range(len(Zp))] for i in range(len(Zp))])
        print(f"exact LDL^T: t I - E > 0 for t = lambda_max*(1+{fac-1:.0e}) = {float(tt):.6e}: {ok}")
    for cw in (0.05, 0.59):
        WZm = [[W[ia][ic] - (F(cw) * gF if ia == ic else 0) for ic in Zs] for ia in Zs]
        print(f"exact: W_Z - {cw} g I > 0: {ldl_pd(WZm)[0]}")

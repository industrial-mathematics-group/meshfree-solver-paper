"""Independent 1-D re-implementation of the linear MUSCL operator (written from the paper's description, not from linop.py's
loop structure) and comparison with linop.build_operator on jittered clouds; plus lattice symbol vs. brute-force eigenvalues."""
import os, sys, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
import linop, lattice_symbols
from math import factorial

def w(r, R):
    y = (r / R) ** 2
    return 1 / (1 + y + y**2 / 2 + y**3 / 6 + y**4 / 24)

def indep_operator(x, kappa, K, orient, a=1.0):
    N = len(x); h = 1.0 / N; R = kappa * h
    nbs = []
    for i in range(N):
        d = (x - x[i] + 0.5) % 1.0 - 0.5
        js = [j for j in range(N) if j != i and abs(d[j]) <= R * (1 + 1e-12)]
        nbs.append((np.array(js), d[js]))
    # derivative weights: weighted LS fit with constant term of degree q, derivative at x_i
    def cweights(off, q):
        Wt = np.diag(w(off, R))
        A = np.vander(off / h, q + 1, increasing=True)          # 1, y, y^2, ... (Taylor scaling irrelevant for d/dx coefficient)
        coef = np.linalg.solve(A.T @ Wt @ A, A.T @ Wt)          # rows: coefficients of y^k
        return coef[1] / h
    # reconstruction: fit p(y) = sum_{k=1}^{K-1} a_k y^k to U_j - U_i, evaluate at midpoint
    def recon(off, r):
        if r == 0: return np.zeros((len(off), len(off)))
        Wt = np.diag(w(off, R))
        A = np.stack([(off / h) ** k for k in range(1, r + 1)], 1)
        coef = np.linalg.solve(A.T @ Wt @ A, A.T @ Wt)
        Am = np.stack([(off / 2 / h) ** k for k in range(1, r + 1)], 1)
        return Am @ coef
    Lm = np.zeros((N, N))
    G = [recon(off, K - 1) for js, off in nbs]
    for i in range(N):
        js, off = nbs[i]
        q = linop.safeguarded_q(len(js), 1, K)
        c = cweights(off, q)
        for s, j in enumerate(js):
            ui = np.zeros(N); ui[i] = 1 - G[i][s].sum(); ui[js] += G[i][s]      # state at midpoint from i
            jsj, offj = nbs[j]; t = list(jsj).index(i)
            uj = np.zeros(N); uj[j] = 1 - G[j][t].sum(); uj[jsj] += G[j][t]
            sg = (1.0 if off[s] > 0 else -1.0) if orient == "geometric" else np.sign(c[s])
            # Rusanov flux with upwinding direction sigma: F* = a (uL+uR)/2 - |a|/2 sigma (uR - uL), uL = state of i side
            Fs = 0.5 * a * (ui + uj) - 0.5 * abs(a) * sg * (uj - ui)
            Fi = np.zeros(N); Fi[i] = a
            Lm[i] -= 2 * c[s] * (Fs - Fi)
    return Lm

rng_ok = True
for K in (2, 3, 4):
    for orient in ("geometric", "aligned"):
        for jit in (0.2, 0.4):
            P, h = linop.make_cloud(60, 1, jit, 3)
            L1 = linop.build_operator(P, h, 2.5, K, [1.0], orient)
            L2 = indep_operator(P[:, 0], 2.5, K, orient)
            err = np.abs(L1 - L2).max() / np.abs(L1).max()
            print(f"K={K} {orient} jitter={jit}: max rel diff linop vs independent = {err:.2e}")
            rng_ok &= err < 1e-10
# consistency: L applied to polynomial data of degree <= K-1? (exactness of derivative for linear data)
P, h = linop.make_cloud(200, 1, 0.2, 0)
x = P[:, 0]
for K in (2, 3, 4):
    L = linop.build_operator(P, h, 2.5, K, [1.0], "geometric")
    u = np.sin(2 * np.pi * x); err = np.abs(L @ u + 2 * np.pi * np.cos(2 * np.pi * x)).max()
    print(f"K={K}: truncation error of -u_x on sin at n=200: {err:.2e}")
# lattice symbol (lattice_symbols.symbol) vs eigenvalues of the assembled operator on a periodic lattice
for kappa in (2.5, 3.5):
    for K in (2, 3, 4, 5):
        n = 48
        lam, norm, q = lattice_symbols.symbol(1, kappa, K, [1.0], m=n + 1, orient="geometric")
        th = np.linspace(-np.pi, np.pi, n + 1)
        P, h = linop.make_cloud(n, 1, 0.0)
        L = linop.build_operator(P, h, kappa, K, [1.0], "geometric") * h
        ev = np.linalg.eigvals(L)
        # every grid wave number 2 pi k / n must be an eigenvalue
        thk = 2 * np.pi * np.arange(n) / n
        ints = np.arange(-n // 2, n // 2)
        row = L[0]
        offs = np.round(((P[:, 0] - P[0, 0] + 0.5) % 1 - 0.5) / h).astype(int)
        lamk = np.array([(row * np.exp(1j * t * offs)).sum() for t in thk])
        dist = max(np.min(np.abs(ev - z)) for z in lamk)
        print(f"lattice kappa={kappa} K={K}: max_k dist(symbol(2 pi k/n), spec L) = {dist:.1e}; max Re symbol = {lamk.real.max():.2e}, max Re eig = {ev.real.max():.2e}")
print("ALL OPERATOR CHECKS PASS" if rng_ok else "OPERATOR MISMATCH")

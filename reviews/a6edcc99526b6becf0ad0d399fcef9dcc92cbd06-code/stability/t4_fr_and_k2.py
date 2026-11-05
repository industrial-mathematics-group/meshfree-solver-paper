"""(a) Local-squares identity of ho_fr.local_squares_1d checked against the assembled matrix: on a periodic lattice of spacing g
(units h=1), -g (L + L^T) must equal sum_j B_j (circulant built from b) entrywise.  (b) E_12 formula of the paper and
P_nm = E_nm / sin^2 t at random t, by direct trig evaluation (independent of the Chebyshev route)."""
import os, sys, numpy as np, sympy as sp
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
import ho_fr, linop
for K, orient in [(2, "geometric"), (3, "geometric"), (4, "geometric"), (4, "aligned")]:
    for g in (0.85, 1.0, 1.15):
        b, d, m, err = ho_fr.local_squares_1d(K, orient, 2.5, g)
        n = 40
        x = (np.arange(n) + 0.5) * g
        L = linop.build_operator((x / (n * g))[:, None], 1.0 / (n * g), 2.5, K, [1.0], orient) / (n * g)
        lhs = -g * (L + L.T)
        B = np.zeros((n, n))
        for j in range(n):
            e = np.zeros(n)
            for k in range(len(b)): e[(j + k) % n] += b[k]
            B += np.outer(e, e)
        print(f"K={K} {orient} g={g}: m={m} d={d} FR err={err:.1e}  max|-g(L+L^T) - sum B_j| = {np.abs(lhs - B).max():.1e} (max|lhs|={np.abs(lhs).max():.2f})")
t = sp.symbols("t")
E = lambda n, m: n * sp.sin(m*t)**2 + m * sp.sin(n*t)**2 - (n+m) * sp.sin(n*t)*sp.cos(n*t)*sp.sin(m*t)*sp.cos(m*t)
c = sp.cos(t)
expr = sp.simplify(sp.expand_trig(E(1, 2) - 2*sp.sin(t)**2*(6*c**2+1)*(1-c**2)))
print("E_12 - 2 sin^2 t (6c^2+1)(1-c^2) =", expr)
# P_10,1 negativity by direct trig: min over t of E(10,1)/sin^2
tt = np.linspace(1e-3, np.pi/2, 200001)
E101 = 10*np.sin(tt)**2 + np.sin(10*tt)**2 - 11*np.sin(10*tt)*np.cos(10*tt)*np.sin(tt)*np.cos(tt)
print("min_t E_{10,1}/sin^2 t =", (E101/np.sin(tt)**2).min())
worst = min((n*np.sin(m*tt)**2 + m*np.sin(n*tt)**2 - (n+m)*np.sin(n*tt)*np.cos(n*tt)*np.sin(m*tt)*np.cos(m*tt)).min()/1 for n in range(1,10) for m in range(1,n+1))
print("min over 1<=m<=n<=9, t of E_nm (float grid) =", worst)

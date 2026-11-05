"""ho_bloch.kreiss_sym uses an eigendecomposition without conditioning check; recompute the Bloch-Kreiss constant at the
reported worst theta with scipy expm for two records of data/ho_bloch_1d.jsonl."""
import os, sys, numpy as np, scipy.linalg as sl
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
from ho_common import bloch_symbols
for (jit, m, seed, K, orient, th) in [(0.4, 32, 1, 4, "geometric", -np.pi), (0.4, 16, 1, 4, "geometric", 4.44e-16), (0.2, 8, 0, 4, "geometric", None)]:
    rng = np.random.default_rng(1000 + seed)
    g = (np.arange(m) + 0.5) / m
    P0 = np.mod(g[:, None] + jit / m * (2 * rng.random((m, 1)) - 1), 1.0)
    thetas = np.linspace(-np.pi, np.pi, 200, endpoint=False) if th is None else [th]
    syms, h = bloch_symbols(P0, 2.5, K, [1.0], orient, thetas)
    ts = np.logspace(-2, 3, 26) * h
    best_eig, best_expm, cmax = 0, 0, 0
    for S in syms:
        ev, X = np.linalg.eig(S); Xi = np.linalg.inv(X); cmax = max(cmax, np.linalg.cond(X))
        best_eig = max(best_eig, max(np.linalg.norm((X * np.exp(t * ev)[None, :]) @ Xi, 2) for t in ts))
        best_expm = max(best_expm, max(np.linalg.norm(sl.expm(t * S), 2) for t in ts))
        # finer time grid
    tsf = np.logspace(-3, 3.5, 400) * h
    fine = max(max(np.linalg.norm(sl.expm(t * S), 2) for t in tsf) for S in syms)
    print(f"jit={jit} m={m} seed={seed} K={K}: eig-based {best_eig:.6f}  expm {best_expm:.6f}  expm fine t-grid {fine:.6f}  max cond(X) {cmax:.1e}")

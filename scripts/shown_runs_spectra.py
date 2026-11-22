"""Spectral abscissa of the semi-discrete operators of the present schemes on the 1-D clouds of the
computations in the paper (linear advection, a = 1, periodic perturbed lattices, weight of Eq. (2.3)).

Uses the operator of w25_stability_comparison.py (same folder): reconstruction of degree K-1 through U_i,
derivative weights of a separate fit of degree q(K) with constant term, aligned orientation for K = 1 and
geometric orientation otherwise (the aligned flux coincides with it at full order).
Clouds: jitter 0.2h with kappa = 2.5 and 5.5 (convergence studies, Sod), jitter 0.4h with kappa = 5.5
(conservation test). Prints max Re(lambda) over the seeds for K = 1..5 (K <= 4 for kappa = 2.5).
Run:  python3 shown_runs_spectra.py [seeds]      (default 3; N = 100, 200, 400, 800)
"""
import sys, os
import numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import w25_stability_comparison as w

CASES = {1: (0, 1, "aligned"), 2: (1, 1, "geo"), 3: (2, 3, "geo"), 4: (3, 3, "geo"), 5: (4, 5, "geo")}
CLOUDS = [(0.2, 2.5), (0.2, 5.5), (0.4, 5.5)]

if __name__ == "__main__":
    seeds = int(sys.argv[1]) if len(sys.argv) > 1 else 3
    for rnd, kap in CLOUDS:
        Ks = [K for K in CASES if kap > 2.5 or K <= 4]
        print(f"== jitter {rnd}h, kappa = {kap}: max Re(lambda) over {seeds} clouds")
        for N in (100, 200, 400, 800):
            res = {K: -np.inf for K in Ks}
            for s in range(seeds):
                x, h = w.grid(N, rnd, s)
                nb = w.nbrs(x, h, kap * h + 1e-12)
                wf = lambda d, h=h: w.wrat(d, kap * h)
                for K in Ks:
                    rd, dd, o = CASES[K]
                    ev = np.linalg.eigvals(w.operator(x, h, nb, rd, dd, True, o, wf))
                    res[K] = max(res[K], ev.real.max())
            print(f"  N = {N:4d}: " + "  ".join(f"K={K}: {res[K]:+.1e}" for K in Ks), flush=True)

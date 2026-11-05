"""Extra checks of scripts/stencil_diagnostics.py.
1. Polynomial exactness: the degree-q weights must differentiate all monomials of degree <= q exactly
   (sum_j c_ij (p(x_j) - p(x_i)) = grad p(x_i)), on the perturbed periodic lattice.
2. Pair defects quoted in the paper but not printed by the script: equal volumes (Sec. 6, "5.7%, 16.7%, 72.8%")
   and Shepard volumes without the smoothing sweep (table caption, "6.2% and 16.9%").
Usage: python3 stencil_extra.py <path to scripts/> [n]"""
import sys, numpy as np
sys.path.insert(0, sys.argv[1]); import stencil_diagnostics as sd
n = int(sys.argv[2]) if len(sys.argv) > 2 else 300
P, L = sd.make_cloud(48, 0.2, 42); idx, off, m = sd.neighbour_table(P, L, 2.5)
for q in (1, 3):
    c = sd.derivative_weights(off, m, 2.5, q, True)
    worst = 0
    for a in sd.exponents(2, q):
        val = np.prod([off[..., d] ** a[d] for d in range(2)], axis=0) * m          # p(x_j)-p(x_i), p(0)=0 locally
        g = np.einsum("nk,nkd->nd", val, c)
        ex = np.zeros(2)
        for d in range(2):
            if a[d] == 1 and sum(a) == 1: ex[d] = 1.0
        worst = max(worst, np.abs(g - ex).max())
    print(f"q={q}: max error differentiating monomials of degree <= {q}: {worst:.2e}")
P, L = sd.make_cloud(n, 0.2, 7); idx, off, m = sd.neighbour_table(P, L, 2.5)
w0 = sd.weight(0.0, 2.5); W = np.where(m, sd.weight((off**2).sum(-1), 2.5), 0.0)
Vraw = 1.0 / (w0 + W.sum(1)); Vraw *= L * L / Vraw.sum()
Vs = sd.shepard_volumes(idx, off, m, 2.5, L * L)
E = np.ones(len(P))
rng = np.random.default_rng(7 + 1); qmix = np.where(rng.random(len(P)) < 0.5, 1, 3)
cs = {q: sd.derivative_weights(off, m, 2.5, q, True) for q in (1, 3)}
cmix = np.where((qmix == 1)[:, None, None], cs[1], cs[3])
for name, V in (("equal volumes", E), ("Shepard, no sweep", Vraw), ("Shepard, one sweep", Vs)):
    d1 = sd.pair_defect(idx, m, cs[1], V); d3 = sd.pair_defect(idx, m, cs[3], V)
    dm = sd.pair_defect(idx, m, cmix, V, mask=lambda i, j: qmix[i] != qmix[j])
    print(f"{n}x{n} perturbed, {name}: pair defect q=1 {100*d1:.1f}%, q=3 {100*d3:.1f}%, mixed {100*dm:.1f}%", flush=True)

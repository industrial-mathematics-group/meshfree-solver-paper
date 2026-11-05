"""Bloch symbols (ho_common.bloch_symbols) vs. brute-force eigenvalues of the full periodic operator built from M copies
of the same supercell: spec(L_full) * h_full must equal the union over theta = 2 pi k / M of spec(Lhat(theta)) * h_bloch."""
import os, sys, numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
import ho_common, linop

def supercell(m, D, jit, seed):
    rng = np.random.default_rng(1000 + seed)
    g = (np.arange(m) + 0.5) / m
    P0 = np.stack(np.meshgrid(*([g] * D), indexing="ij"), axis=-1).reshape(-1, D)
    return np.mod(P0 + jit / m * (2 * rng.random(P0.shape) - 1), 1.0)

for (D, m, M, jit, K, orient) in [(1, 8, 12, 0.2, 2, "geometric"), (1, 8, 10, 0.4, 2, "geometric"), (1, 8, 10, 0.4, 4, "geometric"),
                                  (1, 16, 8, 0.4, 3, "aligned"), (2, 4, 4, 0.2, 2, "geometric"), (2, 4, 3, 0.2, 3, "geometric")]:
    P0 = supercell(m, D, jit, 0)
    a = [1.0] if D == 1 else [1.0, 0.5]
    t1 = 2 * np.pi * np.arange(M) / M
    thetas = t1 if D == 1 else np.array([(x, y) for x in t1 for y in t1])
    syms, hb = ho_common.bloch_symbols(P0, 2.5, K, a, orient, thetas)
    evb = np.concatenate([np.linalg.eigvals(S) for S in syms]) * hb
    Pf, _ = ho_common.supercell_cloud(P0, M)
    hf = 1.0 / (M * m)
    Lf = linop.build_operator(Pf, hf, 2.5, K, a, orient)
    evf = np.linalg.eigvals(Lf) * hf
    d1 = max(np.min(np.abs(evf - z)) for z in evb)
    d2 = max(np.min(np.abs(evb - z)) for z in evf)
    print(f"D={D} m={m} M={M} jit={jit} K={K} {orient}: N={len(Pf)} Hausdorff dist of spectra = {max(d1, d2):.1e}; "
          f"max Re*h full={evf.real.max():.3e} bloch={evb.real.max():.3e}")

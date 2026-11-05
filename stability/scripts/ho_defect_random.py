"""Random defects of density p on a (smoothly deformed) lattice: spectral abscissa, numerical abscissa and Kreiss constants.

Reference lattice s = (i + 1/2) h (per direction); a fraction p of the sites is chosen at random (pairwise at distance
>= 3 h, so that the defects do not overlap) and each is turned into a merge (site removed), insert (particle added at
the midpoint to the next site / at the cell corner in 2-D) or shift (site displaced by 0.3 h, 1-D only) defect; the
cloud is then deformed by x = phi(s), phi(s) = s + A sin(2 pi s)/(2 pi) per coordinate.  Norm: Jacobian volumes.
Usage: python3 ho_defect_random.py D A p n1,n2,... K1,K2,... nseeds out.jsonl [orients]
"""
import json
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import default_times, kreiss, sym_abscissa  # noqa: E402
from linop import build_operator  # noqa: E402

D, A, p = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ns = [int(v) for v in sys.argv[4].split(",")]
Ks = [int(v) for v in sys.argv[5].split(",")]
nseeds, out = int(sys.argv[6]), sys.argv[7]
orients = sys.argv[8].split(",") if len(sys.argv) > 8 else ["geometric"]
kappa = 2.5
a = [1.0] if D == 1 else [1.0, 0.5]
TYPES = ["merge", "insert", "shift"] if D == 1 else ["merge", "insert"]


def defect_cloud(n, seed):
    rng = np.random.default_rng(seed)
    h = 1.0 / n
    g = (np.arange(n) + 0.5) * h
    S = np.stack(np.meshgrid(*([g] * D), indexing="ij"), axis=-1).reshape(-1, D)
    N = len(S)
    ndef = int(round(p * N))
    chosen = []
    order = rng.permutation(N)
    for i in order:
        if len(chosen) == ndef:
            break
        if all(np.abs(np.mod(S[i] - S[j] + 0.5, 1.0) - 0.5).max() >= 3 * h - 1e-12 for j in chosen):
            chosen.append(i)
    types = [TYPES[k] for k in rng.integers(0, len(TYPES), len(chosen))]
    keep = np.ones(N, bool)
    extra = []
    for i, typ in zip(chosen, types):
        if typ == "merge":
            keep[i] = False
        elif typ == "insert":
            extra.append(S[i] + 0.5 * h)
        elif typ == "shift":
            S[i, 0] += 0.3 * h
    S = np.concatenate([S[keep]] + ([np.array(extra)] if extra else []))
    P = np.mod(S + A * np.sin(2 * np.pi * S) / (2 * np.pi), 1.0)
    V = np.prod(1.0 + A * np.cos(2 * np.pi * S), axis=1) * h ** D
    return P, V, h, len(chosen), "".join(t[0] for t in types)


with open(out, "a") as f:
    for n in ns:
        for seed in range(nseeds):
            P, V, h, ndef, types = defect_cloud(n, seed)
            for K in Ks:
                for orient in orients:
                    L = build_operator(P, h, kappa, K, a, orient)
                    alpha = np.linalg.eigvals(L).real.max()
                    om = sym_abscissa(L, V)
                    try:
                        kr = kreiss(L, V, default_times(h))
                    except np.linalg.LinAlgError:          # overflow on blow-up clouds (numpy >= 2.5: "SVD did not converge")
                        kr = float("inf")
                    rec = dict(D=D, A=A, p=p, n=n, N=len(P), h=h, seed=seed, ndef=ndef, K=K, orient=orient,
                               alpha_h=float(alpha * h), omega_V_h=float(om * h), kreiss_V=float(kr))
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    print({k: (round(v, 8) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)

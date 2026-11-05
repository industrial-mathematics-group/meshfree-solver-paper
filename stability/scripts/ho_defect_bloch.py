"""Bloch analysis of a lattice with one defect per supercell of m sites (per direction): the periodic defect array.

1-D defect types: merge (site removed), insert (particle at a midpoint), shift (site displaced by 0.3 h).
2-D defect types: merge (site removed), insert (particle at a cell corner, i.e. the centre of four sites).
Records alpha_h = max_theta max Re eig(Lhat) h and the Kreiss constant max_theta sup_t ||exp(t Lhat)||_2.
Usage: python3 ho_defect_bloch.py D m1,m2,... K1,K2,... ntheta out.jsonl [orients] [types]
"""
import json
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import bloch_symbols  # noqa: E402

D = int(sys.argv[1])
ms = [int(v) for v in sys.argv[2].split(",")]
Ks = [int(v) for v in sys.argv[3].split(",")]
ntheta, out = int(sys.argv[4]), sys.argv[5]
orients = sys.argv[6].split(",") if len(sys.argv) > 6 else ["geometric"]
types = sys.argv[7].split(",") if len(sys.argv) > 7 else (["merge", "insert", "shift"] if D == 1 else ["merge", "insert"])
kappa = 2.5
a = [1.0] if D == 1 else [1.0, 0.5]


def defect_cell(m, typ):
    g = (np.arange(m) + 0.5) / m
    if D == 1:
        g = g.copy()
        if typ == "merge":
            g = np.delete(g, m // 2)
        elif typ == "insert":
            g = np.sort(np.append(g, (m // 2 + 1.0) / m))
        elif typ == "shift":
            g[m // 2] += 0.3 / m
        return g[:, None]
    P = np.stack(np.meshgrid(g, g, indexing="ij"), axis=-1).reshape(-1, 2)
    c = (m // 2) * m + m // 2
    if typ == "merge":
        return np.delete(P, c, axis=0)
    if typ == "insert":
        return np.concatenate([P, [[(m // 2 + 1.0) / m, (m // 2 + 1.0) / m]]])
    raise ValueError(typ)


def kreiss_sym(S, h):
    ts = np.logspace(-2, 3, 26) * h
    ev, X = np.linalg.eig(S)
    Xi = np.linalg.inv(X)
    return max(np.linalg.norm((X * np.exp(t * ev)[None, :]) @ Xi, 2) for t in ts)


with open(out, "a") as f:
    for typ in types:
        for m in ms:
            P0 = defect_cell(m, typ)
            if D == 1:
                thetas = np.linspace(-np.pi, np.pi, ntheta, endpoint=False)
            else:
                t1 = np.linspace(-np.pi, np.pi, ntheta, endpoint=False)
                thetas = np.array([(x, y) for x in t1 for y in t1])
            for K in Ks:
                for orient in orients:
                    syms, h = bloch_symbols(P0, kappa, K, a, orient, thetas, m=m)
                    alph = [np.linalg.eigvals(S).real.max() for S in syms]
                    kr = max(kreiss_sym(S, h) for S in syms)
                    i = int(np.argmax(alph))
                    rec = dict(D=D, type=typ, m=m, K=K, orient=orient, h=h, ntheta=len(thetas), alpha_h=float(alph[i] * h),
                               theta_worst=np.atleast_1d(thetas[i]).tolist(), kreiss=float(kr))
                    f.write(json.dumps(rec) + "\n")
                    f.flush()
                    print({k: (round(v, 10) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)

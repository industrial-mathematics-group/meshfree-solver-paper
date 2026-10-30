"""Smoothly deformed lattices x = phi(s), phi(s) = s + A sin(2 pi s)/(2 pi): the Lax--Nirenberg mechanism.

Reports, for a refinement sequence, the spectral abscissa, the numerical abscissa in the Jacobian-volume norm
(which must stay O(1) if the sharp Garding inequality applies, against O(1/h) for random clouds) and the Kreiss constant.
Usage: python3 ho_deformed.py D kappa A n1,n2,... K1,K2,... out.jsonl [geometric,aligned]
"""
import json
import sys

import numpy as np

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import default_times, deformed_cloud, jacobian_volumes, kreiss, sym_abscissa  # noqa: E402
from linop import build_operator, first_order_operator, neighbours  # noqa: E402

D, kappa, A = int(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
ns = [int(x) for x in sys.argv[4].split(",")]
Ks = [int(x) for x in sys.argv[5].split(",")]
out = sys.argv[6]
orients = sys.argv[7].split(",") if len(sys.argv) > 7 else ["geometric"]
a = [1.0] if D == 1 else [1.0, 0.5]
with open(out, "a") as f:
    for n in ns:
        P, h, S = deformed_cloud(n, D, A)
        V = jacobian_volumes(S, A, h)
        nb = neighbours(P, kappa * h)
        cnt = [len(j) for j, _ in nb]
        for K, orient in [(K, o) for K in Ks for o in (["aligned"] if K == 1 else orients)]:
            L = first_order_operator(P, h, kappa, a, nb=nb) if K == 1 else build_operator(P, h, kappa, K, a, orient, nb=nb)
            ev = np.linalg.eigvals(L)
            om = sym_abscissa(L, V)
            rec = dict(D=D, kappa=kappa, A=A, n=n, N=len(P), h=h, K=K, orient=orient, nmin=min(cnt), nmax=max(cnt),
                       alpha=float(ev.real.max()), alpha_h=float(ev.real.max() * h), omega_V=float(om), omega_V_h=float(om * h))
            if ev.real.max() * h < 1e-2:
                rec["kreiss_V"] = float(kreiss(L, V, default_times(h)))
            f.write(json.dumps(rec) + "\n")
            f.flush()
            print({k: (round(v, 6) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)

"""Bloch-Kreiss constants of 1-D merge/insert arrays at K=3 (m=32), script h vs lattice h = 1/(3m)."""
import sys
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, sys.argv[2])
import numpy as np
import ho_common as hc
from test_defect_bloch_h import bloch_fixed_h
def kreiss_sym(S, h):
    ts = np.logspace(-2, 3, 26) * h
    ev, X = np.linalg.eig(S); Xi = np.linalg.inv(X)
    return max(np.linalg.norm((X * np.exp(t * ev)[None, :]) @ Xi, 2) for t in ts)
th = np.linspace(-np.pi, np.pi, 64, endpoint=False)
m = 32
for typ in ("merge", "insert"):
    g = (np.arange(m) + 0.5) / m
    g = np.delete(g, m // 2) if typ == "merge" else np.sort(np.append(g, (m // 2 + 1.0) / m))
    s1, h1 = hc.bloch_symbols(g[:, None], 2.5, 3, [1.0], "geometric", th)
    s2, h2 = bloch_fixed_h(g[:, None], m, 2.5, 3, [1.0], "geometric", th)
    print(typ, "K=3 m=32 Kreiss script-h %.3f, lattice-h %.3f" % (max(kreiss_sym(S, h1) for S in s1), max(kreiss_sym(S, h2) for S in s2)), flush=True)

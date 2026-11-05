"""alpha_h of the 1-D merge / insert defect arrays (K=2, geometric, 64 thetas) with the script's inferred h vs. the
lattice spacing h = 1/(3m) (radius kappa = 2.5 lattice spacings)."""
import sys
sys.path.insert(0, sys.argv[1]); sys.path.insert(0, sys.argv[2])
import numpy as np
import ho_common as hc
from test_defect_bloch_h import bloch_fixed_h
th = np.linspace(-np.pi, np.pi, 64, endpoint=False)
for typ in ("merge", "insert"):
    for m in (8, 16, 32, 64):
        g = (np.arange(m) + 0.5) / m
        g = np.delete(g, m // 2) if typ == "merge" else np.sort(np.append(g, (m // 2 + 1.0) / m))
        s2, h2 = bloch_fixed_h(g[:, None], m, 2.5, 2, [1.0], "geometric", th)
        a2 = max(np.linalg.eigvals(S).real.max() for S in s2) * h2
        print(f"{typ} m={m}: alpha_h with h=1/(3m): {a2:.2e}", flush=True)

"""Left null vector pi of the single-defect operator (1-D, units h = 1, periodic cell of 64 sites): decay of |pi_i - 1| away
from the defect (Remark on the residual: pi is not locally constant, so no exact local certificate exists).
Usage: python3 ho_defect_pi.py out.md
"""
import sys

import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_defect_cert import defect_sites, operator  # noqa: E402

n = 64
with open(sys.argv[1], "w") as f:
    f.write("| type | K | orient | min pi | max pi | |pi-1| at distance 2, 4, 6, 8, 10, 12 |\n|---|---|---|---|---|---|\n")
    for typ in ("merge", "insert", "shift"):
        for K in (2, 3, 4):
            for orient in ("geometric", "aligned"):
                x, z = defect_sites(n, 1.0, typ, n // 2)
                L = operator(x, float(n), K, orient)
                pi = sl.null_space(L.T)[:, 0]
                pi /= np.mean(pi[:4])
                dist = np.abs(x - z)
                vals = []
                for dd in (2, 4, 6, 8, 10, 12):
                    sel = np.where(np.abs(dist - dd) < 0.6)[0]
                    vals.append(np.abs(pi[sel] - 1).max())
                line = "| %s | %d | %s | %.3f | %.3f | %s |" % (typ, K, orient, pi.min(), pi.max(), ", ".join("%.1e" % v for v in vals))
                f.write(line + "\n")
                print(line)

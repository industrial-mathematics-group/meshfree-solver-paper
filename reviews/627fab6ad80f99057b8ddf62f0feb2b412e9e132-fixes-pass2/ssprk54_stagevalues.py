"""Canonical Shu-Osher form of SSPRK(5,4) (Spiteri-Ruuth) and the stage-value elimination of addendum rem:stagevalues."""
import numpy as np
e = np.eye(5); Y = [np.zeros(5)] * 6
Y[1] = 0.391752226571890 * e[0]
Y[2] = 0.444370493651235 * Y[0] + 0.555629506348765 * Y[1] + 0.368410593050371 * e[1]
Y[3] = 0.620101851488403 * Y[0] + 0.379898148511597 * Y[2] + 0.251891774271694 * e[2]
Y[4] = 0.178079954393132 * Y[0] + 0.821920045606868 * Y[3] + 0.544974750228521 * e[3]
Y[5] = (0.517231671970585 * Y[2] + 0.096059710526147 * Y[3] + 0.063692468666290 * e[3]
        + 0.386708617503269 * Y[4] + 0.226007483236906 * e[4])
A = np.zeros((6, 6)); A[:, :5] = np.array(Y)
def canon(r):
    al = r * A @ np.linalg.inv(np.eye(6) + r * A); return al, (np.eye(6) - al) @ np.ones(6)
lo, hi = 0.5, 3.0
for _ in range(60):
    m = (lo + hi) / 2; al, v = canon(m)
    lo, hi = (m, hi) if (al >= -1e-13).all() and (v >= -1e-13).all() else (lo, m)
al, v = canon(lo); print("C =", lo)
cY3 = al[5, 1] / al[2, 1]; cY5 = al[5, 3] / al[4, 3]
print("unrounded: Y3 %.4f  Y5 %.4f  W5 %.4f  U^n %.4f" % (cY3, cY5, al[5, 4], v[5] - cY3 * v[2] - cY5 * v[4]))
R = lambda x: round(x, 4)
print("from the rounded table: Y3 %.4f" % (R(al[5, 1]) / R(al[2, 1])))

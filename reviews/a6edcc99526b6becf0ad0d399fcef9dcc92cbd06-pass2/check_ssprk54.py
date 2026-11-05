"""Recompute Table 1 of the addendum (canonical Shu-Osher form of SSPRK(5,4) at
r = C) from the published Shu-Osher coefficients of Spiteri-Ruuth, and the
coefficient of U^n in Remark 6.2, to check that the hypotheses of
`ssprk54_negative_coefficient` hold for the actual method."""
import numpy as np

e = np.eye(5)
Y = [np.zeros(5)]
Y.append(0.391752226571890 * e[0])
Y.append(0.555629506348765 * Y[1] + 0.368410593050371 * e[1])
Y.append(0.379898148511597 * Y[2] + 0.251891774271694 * e[2])
Y.append(0.821920045606868 * Y[3] + 0.544974750228521 * e[3])
U = (0.517231671970585 * Y[2] + 0.096059710526147 * Y[3] + 0.063692468666290 * e[3]
     + 0.386708617503269 * Y[4] + 0.226007483236906 * e[4])
A = np.zeros((6, 6))
for k in range(5):
    A[k, :5] = Y[k]
A[5, :5] = U


def canonical(r):
    al = r * A @ np.linalg.inv(np.eye(6) + r * A)
    return al, (np.eye(6) - al) @ np.ones(6)


lo, hi = 0.5, 3.0
for _ in range(60):
    mid = (lo + hi) / 2
    al, v = canonical(mid)
    lo, hi = (mid, hi) if al.min() >= -1e-13 and v.min() >= -1e-13 else (lo, mid)
print("C =", lo)
al, v = canonical(lo)
np.set_printoptions(precision=4, suppress=True)
print("v =", v)
print("alpha =\n", al)
print("U^n coefficient:", v[5] - al[5, 1] * v[2] / al[2, 1] - al[5, 3] * v[4] / al[4, 3])

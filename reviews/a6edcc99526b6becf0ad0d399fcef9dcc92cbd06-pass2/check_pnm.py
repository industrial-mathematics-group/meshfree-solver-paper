"""Floating-point sanity check that the hypothesis `hP` of `k2_lattice_1d`
(P_nm >= 0 on [-1, 1] for 1 <= m <= n <= 9) is satisfiable, i.e. the theorem is not
vacuous, and that it fails for n = 10 (the stated limit kappa < 10).
Uses E_nm(t) = sin^2(t) P_nm(cos t) on a fine grid. Not a proof."""
import numpy as np

t = np.linspace(1e-4, np.pi - 1e-4, 400001)


def P(n, m):
    E = (n * np.sin(m * t) ** 2 + m * np.sin(n * t) ** 2
         - (n + m) * np.sin(n * t) * np.cos(n * t) * np.sin(m * t) * np.cos(m * t))
    return E / np.sin(t) ** 2


worst = min(P(n, m).min() for n in range(1, 10) for m in range(1, n + 1))
print("min over 1<=m<=n<=9:", worst)
print("min P_{10,1}:", P(10, 1).min())

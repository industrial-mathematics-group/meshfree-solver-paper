"""Energy form of the nearest-neighbour K = 2 scheme (Proposition "Exact energy identity") on admissible slopes.

For a 2-periodic grid with gaps alternating between 0.9h and 1.1h (kappa = 1.5, weight of linop.py), prints the smallest
eigenvalue of the form Q(sigma) = sum_i m_i sigma_i (sigma_i - sigma_{i-1}) on R^N and on the hyperplane
sum_i g_i sigma_i = 0 of slopes of periodic grid functions (h = 1).
Usage: python3 ho_nn_admissible.py
"""
import numpy as np


def w(r, R=1.5):
    y = (r / R) ** 2
    return 1 / (1 + y + y * y / 2 + y**3 / 6 + y**4 / 24)


print("| N | min eig on R^N | min eig on admissible slopes |")
print("|---|---|---|")
for N in (4, 8, 16, 32, 64, 128, 256):
    g = np.where(np.arange(N) % 2 == 0, 0.9, 1.1)
    gm = np.roll(g, 1)
    wp, wm = w(g), w(gm)
    m = wm * gm**2 * g**2 / (wp * g**2 + wm * gm**2)
    T = np.diag(m)
    for i in range(N):
        T[i, (i - 1) % N] -= m[i] / 2
        T[(i - 1) % N, i] -= m[i] / 2
    B = np.linalg.svd(g[None, :])[2][1:].T
    print(f"| {N} | {np.linalg.eigvalsh(T)[0]:.3e} | {np.linalg.eigvalsh(B.T @ T @ B)[0]:.3e} |")

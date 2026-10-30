"""Long-time behaviour of the first-order aligned scheme for u_t + u_x = 0 on periodic 1-D clouds.

Exact time integration (scipy expm_multiply) of U' = Q U from u0 = sin(2 pi x) to t = T. The discrete solution
is fitted by A sin(2 pi (x - a_eff t)) + B cos(...) in the l2(pi) sense, giving the effective speed a_eff and the
amplitude; the prediction from the drift beta_bar (first_order_corrector.py) is a_eff = 1 - beta_bar.
Usage: python3 first_order_phase.py jitter kappa T n1,n2,...
"""
import sys

import numpy as np
import scipy.sparse.linalg as spl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from first_order_markov import generator  # noqa: E402
from linop import derivative_weights, make_cloud, neighbours  # noqa: E402

jit, kappa, T = float(sys.argv[1]), float(sys.argv[2]), float(sys.argv[3])
for n in [int(x) for x in sys.argv[4].split(",")]:
    P, h = make_cloud(n, 1, jit, 0)
    nb = neighbours(P, kappa * h)
    Q = generator(P, h, kappa, np.array([1.0]), nb)
    x = P[:, 0]
    U = spl.expm_multiply(T * Q, np.sin(2 * np.pi * x))
    # least squares fit U ~ alpha sin(2 pi x) + beta cos(2 pi x)
    Mx = np.stack([np.sin(2 * np.pi * x), np.cos(2 * np.pi * x)], 1)
    (al, be), *_ = np.linalg.lstsq(Mx, U, rcond=None)
    amp = np.hypot(al, be)
    shift = np.arctan2(-be, al) / (2 * np.pi)          # U ~ amp sin(2 pi (x - shift))
    shift = (shift - T) % 1.0
    shift = shift - 1.0 if shift > 0.5 else shift      # shift relative to the exact T
    beta = np.array([(np.abs(derivative_weights(off, kappa * h, 1, h)[:, 0]) * off[:, 0]).sum() for js, off in nb])
    err = np.sqrt(np.mean((U - np.sin(2 * np.pi * (x - T))) ** 2))
    print(f"jitter={jit} kappa={kappa} n={n} T={T}: a_eff-1={shift / T: .3e}  amplitude={amp:.4f}  rms error={err:.3e}",
          flush=True)

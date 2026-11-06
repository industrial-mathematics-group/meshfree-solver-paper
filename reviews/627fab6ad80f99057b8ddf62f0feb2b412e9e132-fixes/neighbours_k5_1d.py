"""Neighbour counts in 1-D at jitter theta = 0.4, kappa = 5.5 (paper :246 and :620).
Run: python3 reviews/627fab6ad80f99057b8ddf62f0feb2b412e9e132-fixes/neighbours_k5_1d.py"""
import numpy as np
rng = np.random.default_rng(0); N = 200000
x = np.arange(N) + rng.uniform(-0.4, 0.4, N)
c = np.zeros(N, int)
for k in range(1, 8):
    near = np.abs(x[k:] - x[:-k]) <= 5.5
    c[:-k] += near; c[k:] += near
c = c[10:-10]
print('min', c.min(), 'max', c.max(), {v: round(float((c == v).mean()), 4) for v in range(8, 13)})

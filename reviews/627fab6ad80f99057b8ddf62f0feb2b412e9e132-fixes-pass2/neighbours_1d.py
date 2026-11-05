"""Neighbour counts within radius 5.5h of a 1-D lattice with uniform jitter of amplitude theta*h (finding N2)."""
import numpy as np
rng = np.random.default_rng(0)
for th in (0.2, 0.4):
    n = 200000; x = np.arange(n) + rng.uniform(-th, th, n); cnt = np.zeros(n, int)
    for k in range(1, 8):
        cnt += (np.abs(np.roll(x, -k) - x) < 5.5).astype(int) + (np.abs(np.roll(x, k) - x) < 5.5).astype(int)
    cnt = cnt[10:-10]
    print(f"theta={th}: min {cnt.min()}, max {cnt.max()}, share with exactly 9: {(cnt == 9).mean():.4f}")

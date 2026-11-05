# From the independent review of 3 Nov 2026 (reviews/meshfree-solver-paper/stability/), added 4 Nov 2026.
"""Random search for violations of Re lambda <= 0 for K = 2 on 1-D lattices with arbitrary positive weights mu_n, n <= m
(the quadratic form sum mu_n mu_m E_nm(t) of the proof of Thm k2).  Also probes m = 10..14 (beyond the proved range)."""
import numpy as np
rng = np.random.default_rng(0)
t = np.linspace(1e-4, np.pi / 2, 4001)
def worst(m, trials):
    n = np.arange(1, m + 1)
    S, C = np.sin(np.outer(n, t)), np.cos(np.outer(n, t))
    E = (n[:, None, None] * S[None] ** 2 + n[None, :, None] * S[:, None] ** 2
         - (n[:, None, None] + n[None, :, None]) * (S * C)[:, None] * (S * C)[None])
    w = -np.inf
    for _ in range(trials):
        mu = rng.random(m) ** rng.uniform(0.2, 5)            # spread of shapes, some nearly sparse
        if rng.random() < 0.3: mu[rng.random(m) < 0.5] = 0
        if mu.sum() == 0: continue
        q = np.einsum('a,b,abt->t', mu, mu, E) / (mu.sum() ** 2)
        w = max(w, -q.min())                                 # > 0 means a violation (Re lambda > 0)
    return w
for m in (6, 9, 10, 12, 14):
    print(f"m={m}: max over trials of max_t (-quadratic form) = {worst(m, 20000 if m <= 6 else 5000):.3e}")
# the worst case for P_{10,1}: mu concentrated on n = 1 and n = 10
n = np.arange(1, 11); best = -np.inf
for a in np.linspace(0, 1, 2001):
    mu = np.zeros(10); mu[0], mu[9] = 1 - a, a
    S, C = np.sin(np.outer(n, t)), np.cos(np.outer(n, t))
    q = sum(mu[i] * mu[j] * (n[i] * S[j]**2 + n[j] * S[i]**2 - (n[i] + n[j]) * S[i] * C[i] * S[j] * C[j]) for i in (0, 9) for j in (0, 9))
    best = max(best, -q.min())
print(f"mu supported on {{1, 10}}: max violation = {best:.3e}")

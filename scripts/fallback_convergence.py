"""Convergence of the first-order scheme (the MOOD fallback) for smooth linear advection.

Independent NumPy re-implementation (not HyperCloud code) of the first-order meshfree MUSCL scheme,
K = 1: constant interface states, Rusanov flux with the aligned orientation sigma = sign(c_ij^(d)) or the
geometric orientation sigma = sign(x_ij,d), MLS derivative weights of degree q (with constant term),
Heun's method (RK2), time step of the paper with weights c-hat (no constant term) and CFL = 0.2.
Periodic Gaussian pulse u0 = exp(-|x|^2) on [-5,5]^D, velocity (1,...,1), discrete L1 error.
It also prints max_i dt * sum_{j,d} s |c_ij^(d)| (positivity condition, uniform wave speed).
Run:  python3 fallback_convergence.py D kappa T N1,N2,...   e.g.  python3 fallback_convergence.py 2 2.5 1 50,100,200,400
Note: on irregular clouds the first-order scheme advects with a slightly wrong speed (about 0.1 % of the
speed for jitter 0.2 h, kappa = 2.5; see the stability note), which these short runs (T = 1, N <= 400) do not resolve:
the observed orders are pre-asymptotic.
Set Q=3 in the environment for degree-three weights (frozen mode k_div = 4).
"""
import os
import sys, numpy as np
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import stencil_diagnostics as sd
from scipy.spatial import cKDTree

def cloud(n, D, jit, seed=1):
    rng = np.random.default_rng(seed)
    g = np.arange(n)*1.0
    P = np.stack(np.meshgrid(*([g]*D), indexing="ij"), -1).reshape(-1, D)
    P = P + jit*(2*rng.random(P.shape)-1)
    return np.mod(P, n), float(n)

def run(n, D, kappa, jit, orient, T, CFL=0.2, q=int(os.environ.get("Q", "1"))):
    P, L = cloud(n, D, jit)
    idx, off, m = sd.neighbour_table(P, L, kappa)
    c = sd.derivative_weights(off, m, kappa, q, True)      # units of 1/h (h=1)
    ch = sd.derivative_weights(off, m, kappa, q, False)
    h = 10.0/n; c = c/h; ch = ch/h
    a = np.ones(D)
    lam = np.abs(a)
    dt = CFL/np.max(D*(np.abs(ch).sum(1)*lam).sum(-1))
    if orient == "aligned": sig = np.sign(c)
    else: sig = np.sign(off)
    diss = (lam*sig*c).sum(-1)*m        # s*sigma*c summed over d, s=|a_d|
    cen = (c*a).sum(-1)*m
    J = np.where(m, idx, 0)
    X = P*h - 5.0
    u0 = lambda x: np.exp(-(x**2).sum(-1))
    def Lop(u):
        uj = u[J]
        return -(cen*uj).sum(1) + (diss*(uj-u[:,None])).sum(1)
    u = u0(X); t = 0.0
    while t < T-1e-12:
        k = min(dt, T-t)
        u1 = u + k*Lop(u); u = 0.5*(u + u1 + k*Lop(u1)); t += k
    xe = np.mod(X - a*T + 5, 10) - 5
    err = h**D*np.abs(u-u0(xe)).sum()
    # positivity margin rho-related: dt*sum s|c| at first order, uniform speeds
    marg = dt*(np.abs(c).sum(1)*lam).sum(-1).max()
    return err, marg

D = int(sys.argv[1]); kappa=float(sys.argv[2]); T=float(sys.argv[3]); ns=[int(x) for x in sys.argv[4].split(",")]
for jit in (0.0, 0.2):
  for orient in ("aligned","geometric"):
    prev=None
    for n in ns:
        e, mg = run(n, D, kappa, jit, orient, T)
        o = "" if prev is None else f"{np.log(prev[1]/e)/np.log(n/prev[0]):.2f}"
        print(f"D={D} kappa={kappa} jit={jit} {orient:9s} N={n:5d} L1={e:.3e} order={o:>5s} max dt*sum s|c|={mg:.3f}", flush=True)
        prev=(n,e)

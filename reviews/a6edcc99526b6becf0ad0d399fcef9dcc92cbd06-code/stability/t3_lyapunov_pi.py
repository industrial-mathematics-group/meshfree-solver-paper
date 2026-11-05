"""(a) sym_abscissa and kreiss of ho_common vs brute force; (b) robustness of the 'feasible' decisions of ho_lyapunov_exact:
omega_pi is always >= 0 (M 1 = 0), so feasibility hinges on the second-largest eigenvalue of the pi-symmetric part on the
complement of the constants.  Reports that eigenvalue (times h) and the dimension of the numerical null space of L^T."""
import os, sys, numpy as np, scipy.linalg as sl
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "..", "stability", "scripts"))
import ho_common, linop

P, h = linop.make_cloud(100, 1, 0.2, 0)
L = linop.build_operator(P, h, 2.5, 3, [1.0], "geometric")
V = ho_common.volumes(P, h)
s = np.sqrt(V); S = s[:, None] * L / s[None, :]
om_bf = np.linalg.eigvalsh(0.5 * (S + S.T))[-1]
print(f"(a) sym_abscissa {ho_common.sym_abscissa(L, V):.10e}  brute force {om_bf:.10e}")
ts = ho_common.default_times(h)
kr_bf = max(np.linalg.norm(sl.expm(t * S), 2) for t in ts)
print(f"    kreiss {ho_common.kreiss(L, V, ts):.10f}  brute force expm {kr_bf:.10f}")
print("(b) D kappa n seed K orient | sv_min(L^T), sv_2(L^T) | lambda_1*h, lambda_2*h of Pi-sym part (Pi-normalised)")
for (kappa, n, seed, K, orient) in [(2.5, 50, 0, 1, "aligned"), (2.5, 50, 0, 2, "geometric"), (2.5, 100, 0, 2, "geometric"),
                                    (2.5, 200, 0, 2, "geometric"), (2.5, 100, 0, 2, "aligned"), (2.5, 50, 0, 3, "geometric"),
                                    (1.5, 50, 0, 2, "geometric"), (1.5, 100, 1, 2, "geometric")]:
    P, h = linop.make_cloud(n, 1, 0.2, seed)
    L = linop.first_order_operator(P, h, kappa, [1.0]) if K == 1 else linop.build_operator(P, h, kappa, K, [1.0], orient)
    _, sv, vt = sl.svd(L.T)
    pi = vt[-1] / vt[-1].sum()
    if pi.min() <= 0:
        print(kappa, n, seed, K, orient, "pi not positive"); continue
    sq = np.sqrt(pi)
    A = sq[:, None] * L / sq[None, :]
    ev = np.linalg.eigvalsh(0.5 * (A + A.T)) * h
    print(f"  1 {kappa} {n} {seed} {K} {orient} | {sv[-1]:.1e}, {sv[-2]:.1e} | {ev[-1]:.3e}, {ev[-2]:.3e}")

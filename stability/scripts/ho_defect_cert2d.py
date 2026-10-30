"""Local Lyapunov certificates at isolated defects of a 2-D lattice (units h = 1), the 2-D version of ho_defect_cert.py.

Local squares from the Gram matrix G of ho_sos2d.py: -(V L + L^T V) = sum_j B_j, B_j(u) = sum_{m,m'} G_{m m'} u_{j+m} u_{j+m'}
(m, m' in the monomial box [-r, r]^2), each B_j >= 0.  Defect types: merge (site removed), insert (particle at a cell corner).
Zone Z = {|x - z|_inf <= rho}; certificate W_Z with  E(W) = W L + L^T W + sum_{far j} B_j <= t I on the touched set Z'.
Usage: python3 ho_defect_cert2d.py K1,K2 rho1,rho2 out.jsonl [n]
"""
import json
import sys

import cvxpy as cp
import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from linop import build_operator  # noqa: E402

KAPPA = 2.5
A_VEC = [1.0, 0.5]
Ks = [int(v) for v in sys.argv[1].split(",")]
rhos = [int(v) for v in sys.argv[2].split(",")]
out = sys.argv[3]
n = int(sys.argv[4]) if len(sys.argv) > 4 else 32
root = __file__.rsplit("/", 2)[0]


def certificate(typ, K, rho, cW=0.05, CW=20.0):
    G = np.load("%s/data/ho_sos2d_K%d_geometric_G.npy" % (root, K))
    G = 0.5 * (G + G.T)
    ev = np.linalg.eigvalsh(G)
    G = G - min(ev[0], 0.0) * np.eye(len(G)) * 0 if ev[0] > -1e-9 else G       # G is PSD to solver accuracy
    M = len(G)
    r = (int(round(np.sqrt(M))) - 1) // 2
    mons = [(i, j) for i in range(-r, r + 1) for j in range(-r, r + 1)]
    g = np.arange(n) + 0.5
    P = np.stack(np.meshgrid(g, g, indexing="ij"), axis=-1).reshape(-1, 2).astype(float)
    c = (n // 2) * n + n // 2
    z = P[c].copy()
    if typ == "merge":
        P = np.delete(P, c, axis=0)
    else:
        z = z + 0.5
        P = np.concatenate([P, [z]])
    N = len(P)
    L = build_operator(P / n, 1.0 / n, KAPPA, K, A_VEC, "geometric") / n
    pos = {(round(p[0], 6), round(p[1], 6)): i for i, p in enumerate(P)}
    dz = np.abs(P - z)
    dz = np.minimum(dz, n - dz)
    dist = dz.max(axis=1)                                                   # sup-norm distance to the centre
    Z = np.where(dist <= rho + 1e-9)[0]
    nz = len(Z)
    Bsum = np.zeros((N, N))
    nfar = 0
    for j in range(n * n):
        base = np.array([(j // n) + 0.5, (j % n) + 0.5])
        idx = [pos.get((round((base[0] + m[0]) % n, 6), round((base[1] + m[1]) % n, 6))) for m in mons]
        if any(i is None or dist[i] <= rho + 1e-9 for i in idx):
            continue
        nfar += 1
        idx = np.array(idx)
        Bsum[np.ix_(idx, idx)] += G
    # entries of E(W) depend on W only on the touched set T (rows/columns coupled to Z through L); E is supported on
    # Zp = {dist <= rho + max(2 r, 4 kappa)} (missing squares reach 2 r beyond Z, non-lattice rows 2 kappa, coupling another 2 kappa)
    touch = set(Z)
    for i in Z:
        touch |= set(np.where(np.abs(L[i]) > 1e-14)[0]) | set(np.where(np.abs(L[:, i]) > 1e-14)[0])
    T = np.array(sorted(touch))
    Zp = np.where(dist <= rho + max(2 * r, int(np.ceil(4 * KAPPA))) + 1e-9)[0]
    assert set(T) <= set(Zp)
    W0 = np.eye(N)
    W0[np.ix_(Z, Z)] = 0
    E0 = W0 @ L + L.T @ W0 + Bsum
    mask = np.ones((N, N), bool)
    mask[np.ix_(Zp, Zp)] = False
    outside = np.abs(E0[mask]).max()
    assert outside < 1e-10, outside
    Wz = cp.Variable((nz, nz), symmetric=True)
    t = cp.Variable()
    SelT = np.zeros((len(T), nz))
    SelT[np.searchsorted(T, Z), np.arange(nz)] = 1.0
    LTT = L[np.ix_(T, T)]
    dW = SelT @ Wz @ SelT.T                                   # W - W0 on T x T
    dE = dW @ LTT + LTT.T @ dW                                 # E(W) - E0 on T x T
    Psel = np.zeros((len(Zp), len(T)))
    Psel[np.searchsorted(Zp, T), np.arange(len(T))] = 1.0
    Ez = E0[np.ix_(Zp, Zp)] + Psel @ dE @ Psel.T
    prob = cp.Problem(cp.Minimize(t), [Ez << t * np.eye(len(Zp)), Wz >> cW * np.eye(nz), Wz << CW * np.eye(nz)])
    prob.solve(solver=cp.CLARABEL)
    Wv = W0.copy()
    Wv[np.ix_(Z, Z)] = 0.5 * (Wz.value + Wz.value.T)
    Ev = Wv @ L + L.T @ Wv + Bsum
    tv = np.linalg.eigvalsh(0.5 * (Ev + Ev.T)[np.ix_(Zp, Zp)])[-1]
    wz = np.linalg.eigvalsh(Wv[np.ix_(Z, Z)])
    S = Wv @ L + L.T @ Wv
    omW = sl.eigh(0.5 * (S + S.T), Wv, eigvals_only=True)[-1] / 2
    omV = np.linalg.eigvalsh(0.5 * (L + L.T))[-1]
    alpha = np.linalg.eigvals(L).real.max()
    return dict(D=2, type=typ, K=K, orient="geometric", rho=rho, n=n, N=N, nz=nz, nT=len(T), nzp=len(Zp), r=r, nfar=nfar, outside=float(outside),
                status=prob.status, t=float(tv), bound_omega_h=float(tv / (2 * cW)), wmin=float(wz[0]), wmax=float(wz[-1]),
                omegaW_h=float(omW), omegaV_h=float(omV), alpha_h=float(alpha))


with open(out, "a") as f:
    for typ in ("merge", "insert"):
        for K in Ks:
            for rho in rhos:
                rec = certificate(typ, K, rho)
                f.write(json.dumps(rec) + "\n")
                f.flush()
                print({k: (round(v, 10) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)

"""Local Lyapunov certificates at isolated defects of a 1-D lattice, and their superposition (units h = 1).

Lattice sites k + 1/2 (spacing g), neighbourhood radius kappa.  Defect types at a centre z:
  merge  : the site at z is removed            (merging two particles into one leaves a hole of two spacings)
  insert : a particle is added at z            (midpoint between two sites, gap h/2)
  shift  : the site at z is displaced by delta (default 0.3 g)
Local-squares decomposition of the lattice dissipation form (ho_fr.local_squares_1d): -g (L + L^T) = sum_j B_j,
B_j(u) = (sum_k b_k u_{j+k})^2.  For a zone Z = {|x - z| <= rho g} the certificate is a symmetric block W_Z with
    E(W) := W L + L^T W + sum_{far j} B_j  <=  t I   on the touched set Z',   cW I <= W_Z <= CW I,   W = g I outside Z,
where "far" squares are those whose support avoids Z.  t = t(rho) is minimized (SDP, CLARABEL).  Because
sum_far B_j <= 0 this gives  u^T (W L + L^T W) u <= t |u_{Z'}|^2  for every cloud containing the defect, and the
zone blocks of distinct defects superpose when the zones are separated by more than 2 kappa + d.

Usage:
  python3 ho_defect_cert.py cert K1,K2 orient g1,g2 rho1,rho2 out.jsonl            (single-defect certificates)
  python3 ho_defect_cert.py super K orient rho ndef n A seed out.jsonl              (multi-defect check, deformation amplitude A)
"""
import json
import sys

import cvxpy as cp
import numpy as np
import scipy.linalg as sl

sys.path.insert(0, __file__.rsplit("/", 1)[0])
from ho_common import kreiss  # noqa: E402
from ho_fr import local_squares_1d  # noqa: E402
from linop import build_operator  # noqa: E402

KAPPA = 2.5
TYPES = ("merge", "insert", "shift")


def defect_sites(n, g, typ, k, delta=0.3):
    """Sites of a periodic cell of n lattice sites (spacing g, period n g) with one defect near site k; returns (x, centre)."""
    x = (np.arange(n) + 0.5) * g
    if typ == "merge":
        return np.delete(x, k), x[k]
    if typ == "insert":
        return np.sort(np.append(x, x[k] + 0.5 * g)), x[k] + 0.5 * g
    if typ == "shift":
        y = x.copy()
        y[k] += delta * g
        return y, x[k]
    raise ValueError(typ)


def operator(x, period, K, orient):
    """L in units h = 1 for particles x on a periodic cell of length `period` (torus rescaled to 1)."""
    return build_operator((x / period)[:, None], 1.0 / period, KAPPA, K, [1.0], orient) / period


def far_squares(x, period, b, g, centres, rho):
    """sum of B_j over lattice-site squares whose support stays at distance > rho g from every centre."""
    N = len(x)
    pos = {round(v, 6): i for i, v in enumerate(x)}
    dist = np.full(N, np.inf)
    for z in centres:
        dz = np.abs(x - z)
        dist = np.minimum(dist, np.minimum(dz, period - dz))
    Bsum = np.zeros((N, N))
    for i in range(N):
        idx = [pos.get(round((x[i] + k * g) % period, 6)) for k in range(len(b))]
        if any(j is None or dist[j] <= rho * g + 1e-9 for j in idx):
            continue
        e = np.zeros(N)
        e[idx] = b
        Bsum += np.outer(e, e)
    return Bsum, dist


def certificate(typ, K, orient, g, rho, n=64, cW=0.05, CW=20.0):
    b, d, m, err = local_squares_1d(K, orient, KAPPA, g)
    x, z = defect_sites(n, g, typ, n // 2)
    period = n * g
    N = len(x)
    L = operator(x, period, K, orient)
    Bsum, dist = far_squares(x, period, b, g, [z], rho)
    Z = np.where(dist <= rho * g + 1e-9)[0]
    nz = len(Z)
    touch = set(Z)
    for i in Z:
        touch |= set(np.where(np.abs(L[i]) > 1e-14)[0]) | set(np.where(np.abs(L[:, i]) > 1e-14)[0])
    Zp = np.array(sorted(touch))
    W0 = g * np.eye(N)
    W0[np.ix_(Z, Z)] = 0
    E0 = W0 @ L + L.T @ W0 + Bsum
    mask = np.ones((N, N), bool)
    mask[np.ix_(Zp, Zp)] = False
    assert np.abs(E0[mask]).max() < 1e-11, "E(W) is not supported on the touched set"
    Wz = cp.Variable((nz, nz), symmetric=True)
    t = cp.Variable()
    Sel = np.zeros((N, nz))
    Sel[Z, np.arange(nz)] = 1.0
    E = (W0 + Sel @ Wz @ Sel.T) @ L + L.T @ (W0 + Sel @ Wz @ Sel.T) + Bsum
    Ez = E[Zp][:, Zp]
    prob = cp.Problem(cp.Minimize(t), [Ez << t * np.eye(len(Zp)), Wz >> cW * g * np.eye(nz), Wz << CW * g * np.eye(nz)])
    prob.solve(solver=cp.CLARABEL)
    Wv = W0.copy()
    Wv[np.ix_(Z, Z)] = 0.5 * (Wz.value + Wz.value.T)
    Ev = Wv @ L + L.T @ Wv + Bsum
    tv = np.linalg.eigvalsh(0.5 * (Ev + Ev.T)[np.ix_(Zp, Zp)])[-1]           # a posteriori residual
    wz = np.linalg.eigvalsh(Wv[np.ix_(Z, Z)]) / g
    S = Wv @ L + L.T @ Wv
    omW = sl.eigh(0.5 * (S + S.T), Wv, eigvals_only=True)[-1] / 2
    omV = np.linalg.eigvalsh(0.5 * (L + L.T))[-1]
    rec = dict(type=typ, K=K, orient=orient, g=g, rho=rho, n=n, nz=nz, nzp=len(Zp), d=d, m=m, fr_err=err, status=prob.status,
               t=float(tv), bound_omega_h=float(tv / (2 * cW * g)), wmin=float(wz[0]), wmax=float(wz[-1]),
               omegaW_h=float(omW), omegaV_h=float(omV))
    return rec, Wv[np.ix_(Z, Z)], Z - Z.min()


def superposition(K, orient, rho, ndef, n, A, seed, out):
    """Cloud of n lattice sites (smoothly deformed by x -> x + A sin(2 pi x / period) period / (2 pi)) with ndef random defects
    separated by >= 2 rho + 20 sites; W assembled from the single-defect certificates at the local spacing g = phi'(z)."""
    rng = np.random.default_rng(seed)
    period = float(n)
    sep = 2 * rho + 20
    while True:
        ks = np.sort(rng.choice(n, ndef, replace=False))
        gaps = np.diff(np.concatenate([ks, [ks[0] + n]]))
        if gaps.min() >= sep:
            break
    types = [TYPES[i] for i in rng.integers(0, 3, ndef)]
    # build the lattice-with-defects in the reference coordinate, then deform
    s = list((np.arange(n) + 0.5))
    centres_s = []
    for k, typ in zip(ks, types):
        z = k + 0.5
        if typ == "merge":
            s.remove(z)
        elif typ == "insert":
            s.append(z + 0.5)
            z = z + 0.5
        elif typ == "shift":
            s[s.index(z)] = z + 0.3
        centres_s.append(z)
    s = np.sort(np.array(s))
    phi = lambda u: u + A * np.sin(2 * np.pi * u / period) * period / (2 * np.pi)   # noqa: E731
    dphi = lambda u: 1 + A * np.cos(2 * np.pi * u / period)                           # noqa: E731
    x = phi(s)
    N = len(x)
    L = operator(x, period, K, orient)
    # weight: Jacobian volumes, replaced by the certificate blocks (scaled by g_A) around each defect
    W = np.diag(dphi(s))
    ts = []
    for z, typ in zip(centres_s, types):
        gA = float(dphi(z))
        rec, WZ, _ = certificate(typ, K, orient, gA, rho)
        ts.append(rec["t"])
        Z = np.where(np.minimum(np.abs(s - z), period - np.abs(s - z)) <= rho + 1e-9)[0]
        Z = Z[np.argsort(np.mod(s[Z] - z + period / 2, period))]        # order by position relative to the centre (periodic wrap)
        assert len(Z) == WZ.shape[0], (len(Z), WZ.shape)
        W[np.ix_(Z, Z)] = WZ
    S = W @ L + L.T @ W
    omW = sl.eigh(0.5 * (S + S.T), W, eigvals_only=True)[-1] / 2
    V = dphi(s)
    omV = sl.eigh(0.5 * (np.diag(V) @ L + L.T @ np.diag(V)), np.diag(V), eigvals_only=True)[-1] / 2
    alpha = np.linalg.eigvals(L).real.max()
    ew = np.linalg.eigvalsh(W)
    kr = kreiss(L, V, np.logspace(-2, 3, 26))
    rec = dict(K=K, orient=orient, rho=rho, ndef=ndef, n=n, A=A, seed=seed, types="".join(t[0] for t in types),
               t_max=float(max(ts)), omegaW_h=float(omW), omegaV_h=float(omV), alpha_h=float(alpha),
               wmin=float(ew[0]), wmax=float(ew[-1]), kreiss_V=float(kr))
    with open(out, "a") as f:
        f.write(json.dumps(rec) + "\n")
    print(rec, flush=True)


if __name__ == "__main__":
    mode = sys.argv[1]
    if mode == "cert":
        Ks = [int(v) for v in sys.argv[2].split(",")]
        orient = sys.argv[3]
        gs = [float(v) for v in sys.argv[4].split(",")]
        rhos = [int(v) for v in sys.argv[5].split(",")]
        out = sys.argv[6]
        with open(out, "a") as f:
            for typ in TYPES:
                for K in Ks:
                    for g in gs:
                        for rho in rhos:
                            rec, _, _ = certificate(typ, K, orient, g, rho)
                            f.write(json.dumps(rec) + "\n")
                            f.flush()
                            print({k: (round(v, 10) if isinstance(v, float) else v) for k, v in rec.items()}, flush=True)
    else:
        K, orient, rho, ndef, n, A, seed, out = int(sys.argv[2]), sys.argv[3], int(sys.argv[4]), int(sys.argv[5]), int(sys.argv[6]), float(sys.argv[7]), int(sys.argv[8]), sys.argv[9]
        superposition(K, orient, rho, ndef, n, A, seed, out)

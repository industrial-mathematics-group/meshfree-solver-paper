"""Geometric diagnostics of the MLS derivative stencils used by the meshfree MUSCL scheme.

Independent NumPy re-implementation of the stencil construction (not HyperCloud code), used to
quantify properties discussed in the paper on the point clouds of the experiments:

  * the l1 norm h * sum_{j,d} |c_ij^(d)| of the first-derivative weights (it sets the CFL time step),
    on average and its maximum over the particles (the maximum decides the time step),
  * the row sums sum_j c_ij with and without the constant term in the fit, and the relative
    difference of the l1 norms with and without the constant term,
  * the sign condition  sign(c_ij^(d)) = sign((x_j - x_i)_d)  of the positivity result
    (share of entries, share of particles with at least one violation, share of the l1 norm),
  * the pair (antisymmetry) defect  V_i c_ij + V_j c_ji  that measures the conservation error,
    for equal degrees and for pairs of particles whose derivative fits have different degrees.

Cloud: periodic Cartesian lattice of spacing h, optionally with uniform jitter of amplitude 0.2 h per
axis, support radius R = 2.5 h, weight w(r) = 1 / (1 + y + y^2/2 + y^3/6 + y^4/24), y = r^2 / R^2,
Shepard volumes with one smoothing sweep (the pair defects are also printed without the sweep and with equal
volumes, and the share of pairs on which the aligned orientations of the two particles disagree).
Run:  python3 stencil_diagnostics.py [n]   (n = 300 for the perturbed column of Table "Stencil diagnostics")
"""
import itertools
import sys
from math import factorial

import numpy as np
from scipy.spatial import cKDTree

H = 1.0
ALPHA = 1.0


def weight(r2, R):
    y = ALPHA * r2 / R**2
    return 1.0 / (1.0 + y * (1.0 + y * (0.5 + y * (1.0 / 6.0 + y / 24.0))))


def exponents(D, q):
    """Multi-indices of degree 1..q, degree by degree (x before y), as in HyperCloudCore."""
    res = []
    for deg in range(1, q + 1):
        cur = [t for t in itertools.product(range(deg + 1), repeat=D) if sum(t) == deg]
        cur.sort(key=lambda t: (-max(t), tuple(reversed(t))))
        res += cur
    return res


def taylor_basis(Y, exps):
    """Y: (..., D) offsets -> (..., B) Taylor monomials y^a / a!."""
    cols = []
    for a in exps:
        c = np.ones(Y.shape[:-1])
        for d, ad in enumerate(a):
            c = c * Y[..., d] ** ad / factorial(ad)
        cols.append(c)
    return np.stack(cols, axis=-1)


def make_cloud(n, jitter, seed):
    rng = np.random.default_rng(seed)
    g = np.arange(n) * H
    X, Y = np.meshgrid(g, g, indexing="ij")
    P = np.stack([X.ravel(), Y.ravel()], axis=1)
    P += jitter * H * (2.0 * rng.random(P.shape) - 1.0)
    return np.mod(P, n * H), n * H


def neighbour_table(P, L, R):
    """Padded neighbour table: idx (N, K) with -1 padding, offsets (N, K, D) (periodic minimum image)."""
    tree = cKDTree(P, boxsize=L)
    lists = tree.query_ball_point(P, R + 1e-12)
    lists = [sorted(j for j in l if j != i) for i, l in enumerate(lists)]
    K = max(len(l) for l in lists)
    N, D = P.shape
    idx = -np.ones((N, K), dtype=int)
    for i, l in enumerate(lists):
        idx[i, :len(l)] = l
    off = np.zeros((N, K, D))
    m = idx >= 0
    d = P[np.where(m, idx, 0)] - P[:, None, :]
    d -= L * np.round(d / L)
    off[m] = d[m]
    return idx, off, m


def derivative_weights(off, m, R, q, intercept, eps0=1e-10, chunk=20000):
    """First-derivative weights (N, K, D) of the degree-q MLS fits (zero on padded slots)."""
    N, K, D = off.shape
    exps = exponents(D, q)
    out = np.zeros((N, K, D))
    for s in range(0, N, chunk):
        o, mm = off[s:s + chunk], m[s:s + chunk]
        w = np.where(mm, weight((o**2).sum(-1), R), 0.0)
        P = taylor_basis(o / H, exps)
        if intercept:
            P = np.concatenate([np.ones(P.shape[:-1] + (1,)), P], axis=-1)
        B = P.shape[-1]
        Nm = np.einsum("nk,nka,nkb->nab", w, P, P)
        tr = np.trace(Nm, axis1=1, axis2=2)
        Nm += (eps0 * tr / B)[:, None, None] * np.eye(B)
        C = np.linalg.solve(Nm, np.transpose(P * w[..., None], (0, 2, 1)))   # (n, B, K)
        k0 = 1 if intercept else 0
        out[s:s + chunk] = np.transpose(C[:, k0:k0 + D, :], (0, 2, 1)) / H
    return out


def shepard_volumes(idx, off, m, R, area, sweep=True):
    """Shepard volumes 1/sum_j w_ij, with one smoothing sweep unless sweep=False, scaled to the area."""
    w0 = weight(0.0, R)
    W = np.where(m, weight((off**2).sum(-1), R), 0.0)
    S = w0 + W.sum(1)
    V = 1.0 / S
    if not sweep:
        return V * area / V.sum()
    Vt = w0 / S * V + (np.where(m, W / S[np.where(m, idx, 0)] * V[np.where(m, idx, 0)], 0.0)).sum(1)
    return Vt * area / Vt.sum()


def pair_defect(idx, m, c, V, mask=None):
    """sum |V_i c_ij + V_j c_ji| / sum (|V_i c_ij| + |V_j c_ji|) over unordered neighbour pairs."""
    N, K = idx.shape
    slot = {}
    for i in range(N):
        for k in range(K):
            if m[i, k]:
                slot[(i, idx[i, k])] = k
    num = den = 0.0
    for (i, j), k in slot.items():
        if j > i and (mask is None or mask(i, j)):
            cij, cji = c[i, k], c[j, slot[(j, i)]]
            num += np.abs(V[i] * cij + V[j] * cji).sum()
            den += np.abs(V[i] * cij).sum() + np.abs(V[j] * cji).sum()
    return num / den


def sign_mismatch(idx, m, c):
    """Share of pairs and directions with sign(c_ij^(d)) = sign(c_ji^(d)) (both nonzero) and their share of
    sum(|c_ij| + |c_ji|): on these the two particles orient the aligned Rusanov flux differently."""
    N, K = idx.shape; slot = {}
    for i in range(N):
        for k in range(K):
            if m[i, k]: slot[(i, idx[i, k])] = k
    cnt = tot = 0; wbad = wtot = 0.0
    D = c.shape[-1]
    for (i, j), k in slot.items():
        if j > i:
            a, b = c[i, k], c[j, slot[(j, i)]]
            tol = 1e-10*max(np.abs(a).max(), np.abs(b).max()); same = (a*b > 0) & (np.abs(a) > tol) & (np.abs(b) > tol)
            cnt += same.sum(); tot += D
            wbad += (np.abs(a) + np.abs(b))[same].sum(); wtot += (np.abs(a) + np.abs(b)).sum()
    return cnt/tot, wbad/wtot


def diagnostics(n=48, jitter=0.2, R=2.5, seed=42, pairs=True):
    P, L = make_cloud(n, jitter, seed)
    idx, off, m = neighbour_table(P, L, R)
    V = shepard_volumes(idx, off, m, R, L * L)
    V0 = shepard_volumes(idx, off, m, R, L * L, sweep=False)
    Veq = np.full(len(P), L * L / len(P))
    nnb = m.sum(1)
    out = {"N": len(P), "mean_nb": nnb.mean(), "min_nb": nnb.min(), "max_nb": nnb.max()}
    cs = {}
    sgn = np.sign(off)
    for q in (1, 3):
        c = derivative_weights(off, m, R, q, True)
        chat = derivative_weights(off, m, R, q, False)
        cs[q] = c
        l1 = H * np.abs(c).sum((1, 2))
        l1hat = H * np.abs(chat).sum((1, 2))
        rowhat = np.abs(chat.sum(1)).sum(1) / np.abs(chat).sum((1, 2))
        row = np.abs(c.sum(1)).sum(1) / np.abs(c).sum((1, 2))
        viol = (sgn * c < 0) & m[..., None]
        negshare = np.clip(-sgn * c, 0, None).sum((1, 2)) / np.abs(c).sum((1, 2))
        out[q] = dict(l1=l1.mean(), l1max=l1.max(), l1hat=l1hat.mean(), l1hatmax=l1hat.max(),
                      reldiff=(np.abs(l1 - l1hat) / l1hat).max(),
                      row=row.max(), rowhat=rowhat.mean(), rowhat_max=rowhat.max(),
                      neg_frac=viol.sum() / (m.sum() * P.shape[1]), neg_particles=viol.any((1, 2)).mean(),
                      neg_share=negshare.mean(), neg_share_max=negshare.max(),
                      pair=pair_defect(idx, m, c, V) if pairs else np.nan,
                      pair_nosweep=pair_defect(idx, m, c, V0) if pairs else np.nan,
                      pair_equal=pair_defect(idx, m, c, Veq) if pairs else np.nan,
                      mismatch=sign_mismatch(idx, m, c) if pairs else (np.nan, np.nan))
    if pairs:
        rng = np.random.default_rng(seed + 1)
        qmix = np.where(rng.random(len(P)) < 0.5, 1, 3)
        cmix = np.where((qmix == 1)[:, None, None], cs[1], cs[3])
        out["mixed_pairs"] = pair_defect(idx, m, cmix, V, mask=lambda i, j: qmix[i] != qmix[j])
        out["mixed_pairs_equal"] = pair_defect(idx, m, cmix, Veq, mask=lambda i, j: qmix[i] != qmix[j])
    out["V_spread"] = (V.min() / H**2, V.max() / H**2)
    return out


def report(res, title):
    print(f"{title}: N = {res['N']}, neighbours mean/min/max = {res['mean_nb']:.2f}/{res['min_nb']}/{res['max_nb']}, "
          f"V/h^2 in [{res['V_spread'][0]:.3f}, {res['V_spread'][1]:.3f}]")
    for q in (1, 3):
        r = res[q]
        print(f"  q={q}: h*sum|c| mean {r['l1']:.3f} max {r['l1max']:.3f} "
              f"(no constant term: mean {r['l1hat']:.3f} max {r['l1hatmax']:.3f}; max rel. difference {100*r['reldiff']:.1f}%)")
        print(f"        row sums: with constant term max {r['row']:.1e}; without: mean {100*r['rowhat']:.1f}% max {100*r['rowhat_max']:.1f}%")
        print(f"        sign condition violated by {100*r['neg_frac']:.1f}% of the entries, at {100*r['neg_particles']:.0f}% of the particles, "
              f"share of sum|c| mean {100*r['neg_share']:.2f}% max {100*r['neg_share_max']:.1f}%; pair defect {100*r['pair']:.1f}%")
        print(f"        pair defect without the smoothing sweep {100*r['pair_nosweep']:.1f}%, with equal volumes {100*r['pair_equal']:.1f}%")
        print(f"        pairs x directions with sign(c_ij)=sign(c_ji): {100*r['mismatch'][0]:.2f}% (weight share {100*r['mismatch'][1]:.2f}%)")
    if "mixed_pairs" in res:
        print(f"  pairs with degrees 1 and 3: pair defect {100*res['mixed_pairs']:.1f}%, with equal volumes {100*res['mixed_pairs_equal']:.1f}%")


if __name__ == "__main__":
    report(diagnostics(jitter=0.0), "lattice 48x48")
    report(diagnostics(jitter=0.2), "perturbed 48x48")
    n = int(sys.argv[1]) if len(sys.argv) > 1 else 300
    report(diagnostics(n=n, jitter=0.2, seed=7), f"perturbed {n}x{n}")

"""Fejer-Riesz factorization of a nonnegative cosine polynomial with a (known-order) zero at theta = 0."""
import numpy as np
from numpy.polynomial import chebyshev as C, polynomial as Pl


def fejer_riesz(c, tol=1e-9):
    """c[k], k = 0..d: f(theta) = c0 + 2 sum_{k>=1} c_k cos(k theta) >= 0.  Returns real b_0..b_d with |sum b_k z^k|^2 = f(theta), z = e^{i theta}."""
    d = len(c) - 1
    cheb = np.concatenate([[c[0]], 2 * np.asarray(c[1:])])
    F = C.cheb2poly(cheb)                        # power series in x = cos theta
    # deflate zeros at x = 1
    m = 0
    while True:
        q, r = Pl.polydiv(F, [1.0, -1.0])        # F = q (x - 1) + r
        if abs(r[0]) > tol * np.abs(F).max():
            break
        F, m = q, m + 1
    F = F * (-1) ** m                            # (x-1)^m = (-1)^m (1-x)^m, F now >= 0 on [-1,1] (after deflation)
    g = C.poly2cheb(F)
    g = np.concatenate([[g[0]], g[1:] / 2])      # back to the c-convention
    dg = len(g) - 1
    full = np.concatenate([g[::-1], g[1:]])      # Laurent coefficients z^-dg .. z^dg
    roots = np.roots(full[::-1])
    inside = [z for z in roots if abs(z) < 1]
    assert len(inside) == dg, (roots, dg)
    bg = np.real(np.poly(inside)[::-1]) if dg > 0 else np.array([1.0])
    # factor (1 - cos theta)^m = |1 - z|^{2m} / 2^m
    b = bg
    for _ in range(m):
        b = Pl.polymul(b, [1.0, -1.0])
    th = np.linspace(0, np.pi, 2001)
    f = c[0] + 2 * sum(c[k] * np.cos(k * th) for k in range(1, d + 1))
    bb = np.abs(Pl.polyval(np.exp(1j * th), b)) ** 2
    scale = np.sqrt(np.max(f) / np.max(bb))
    b = b * scale
    bb = bb * scale ** 2
    return b, m, np.max(np.abs(f - bb)) / max(np.max(f), 1e-300)


def lattice_rows(K, orient, kappa=2.5, g=1.0, n=64, q=None):
    """Row of the operator of the uniform 1-D lattice with spacing g h and radius kappa h, in units h = 1.
    By dilation, L^{(g)} = L[spacing h, radius kappa h / g] / g.  Returns (ell, d): ell[k + d] = L_{0,k}, k = -d..d."""
    import sys
    sys.path.insert(0, __file__.rsplit("/", 1)[0])
    from linop import build_operator
    h = 1.0 / n
    P = (np.arange(n) + 0.5)[:, None] * h
    L = build_operator(P, h, kappa / g, K, [1.0], orient, q=q) * h / g
    row = L[0]
    d = max(k for k in range(1, n // 2) if abs(row[k]) > 1e-14 or abs(row[-k]) > 1e-14)
    ell = np.array([row[k % n] for k in range(-d, d + 1)])
    return ell, d


def local_squares_1d(K, orient, kappa=2.5, g=1.0, n=64, q=None):
    """Fejer-Riesz factor b of the lattice dissipation form in the Jacobian-volume weight:
    -(g h) (L + L^T) = sum_j B_j,  B_j(u) = (sum_k b_k u_{j+k})^2   (units h = 1; the weight g h cancels the 1/(g h) of L up to the g-dependence of the weights).
    Returns (b, d, m, relerr): b_0..b_d, half-bandwidth d of L, zero order 2m of the symbol at theta = 0, relative factorization error."""
    ell, d = lattice_rows(K, orient, kappa, g, n, q)
    c = np.array([-g * (ell[d + k] + ell[d - k]) for k in range(d + 1)])
    c[0] = -2 * g * ell[d]
    b, m, err = fejer_riesz(c)
    return b, d, m, err

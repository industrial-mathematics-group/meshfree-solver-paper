"""Exact certificate for the von Neumann condition of the K = 2 scheme on one-dimensional lattices.

With t = theta/2 and the Chebyshev polynomials T_n, U_{n-1} in c = cos t,
  E_nm(t) = n sin^2(mt) + m sin^2(nt) - (n+m) sin(nt)cos(nt) sin(mt)cos(mt) = sin^2(t) P_nm(c),
  P_nm = n U_{m-1}^2 + m U_{n-1}^2 - (n+m) U_{n-1} T_n U_{m-1} T_m.
The script checks P_nm >= 0 on [-1, 1] in exact rational arithmetic (square-free decomposition and Sturm root
counting) for 1 <= m <= n <= NMAX, and reports the first pair that fails.
"""
import sys

import sympy as sp

c = sp.symbols("c")
NMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 12


def T(n):
    return sp.chebyshevt(n, c)


def U(n):
    return sp.chebyshevu(n, c)


def nonneg_on_interval(P):
    """Exact test of P >= 0 on [-1, 1]: with the square-free decomposition P = a * prod f_i^k_i, P >= 0 on
    [-1, 1] iff Q = a * prod_{k_i odd} f_i (square free) has no root in the open interval and Q(x0) >= 0 at a
    point x0 where Q does not vanish."""
    P = sp.Poly(sp.expand(P), c, domain="QQ")
    if P.is_zero:
        return True
    a, facs = P.sqf_list()
    Q = sp.Poly(a, c, domain="QQ")
    for f, k in facs:
        if k % 2 == 1:
            Q = Q * f
    inner = Q.count_roots(-1, 1) - (Q.eval(-1) == 0) - (Q.eval(1) == 0)
    if inner > 0:
        return False
    x0 = sp.Rational(1, 3)
    while Q.eval(x0) == 0:
        x0 /= 2
    return Q.eval(x0) > 0


ok = []
for n in range(1, NMAX + 1):
    for m in range(1, n + 1):
        P = n * U(m - 1) ** 2 + m * U(n - 1) ** 2 - (n + m) * U(n - 1) * T(n) * U(m - 1) * T(m)
        good = nonneg_on_interval(P)
        if not good:
            print(f"P_{n},{m} takes negative values on [-1, 1]")
            sys.exit(0)
        ok.append((n, m))
print(f"P_nm >= 0 on [-1, 1] for all 1 <= m <= n <= {NMAX}")

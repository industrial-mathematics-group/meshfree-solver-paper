"""Independent checks of fv_reference/fv.py: flux consistency, Galilean/rotational symmetry of the x and y sweeps,
and a Sod shock tube (in x and in y) against the exact Riemann solution.
Run from the repo root: python3 reviews/<name>/test_fv.py"""
import os, sys, numpy as np
ROOT = os.environ.get("REPO", os.path.abspath(os.path.join(os.path.dirname(__file__), "..", "..")))
sys.path.insert(0, os.path.join(ROOT, "fv_reference"))
os.chdir(os.environ.get("OUT", "."))
import fv
from scipy.optimize import brentq
g = fv.G

def exact_sod(x, t, x0=0.5):
    rL, uL, pL, rR, uR, pR = 1.0, 0.0, 1.0, 0.125, 0.0, 0.1
    cL, cR = np.sqrt(g*pL/rL), np.sqrt(g*pR/rR)
    def f(p, r, pk, c):
        if p > pk:
            A = 2/((g+1)*r); B = (g-1)/(g+1)*pk; return (p-pk)*np.sqrt(A/(p+B))
        return 2*c/(g-1)*((p/pk)**((g-1)/(2*g))-1)
    ps = brentq(lambda p: f(p, rL, pL, cL)+f(p, rR, pR, cR), 1e-6, 10)
    us = 0.5*(f(ps, rR, pR, cR)-f(ps, rL, pL, cL))
    rsL = rL*(ps/pL)**(1/g); rsR = rR*((ps/pR+(g-1)/(g+1))/((g-1)/(g+1)*ps/pR+1))
    S = cR*np.sqrt((g+1)/(2*g)*ps/pR+(g-1)/(2*g)); csL = cL*(ps/pL)**((g-1)/(2*g))
    xi = (x-x0)/t; r = np.empty_like(x)
    head, tail = -cL, us-csL
    r[xi < head] = rL
    fan = (xi >= head) & (xi < tail)
    u = 2/(g+1)*(cL+xi[fan]); c = cL-(g-1)/2*u; r[fan] = rL*(c/cL)**(2/(g-1))
    r[(xi >= tail) & (xi < us)] = rsL; r[(xi >= us) & (xi < S)] = rsR; r[xi >= S] = rR
    return r

class Sod:
    def __init__(self, axis): self.axis = axis
    Lx = Ly = 1.0; tend = 0.2
    def init(self, X, Y):
        Z = X if self.axis == 0 else Y
        L = fv.cons(1.0, 0, 0, 1.0); R = fv.cons(0.125, 0, 0, 0.1)
        return np.where((Z < 0.5)[None], L[:, None, None], R[:, None, None])
    def bc(self, U, X, Y, t):
        n = fv.NG
        U[:, :n, :] = U[:, n:n+1, :]; U[:, -n:, :] = U[:, -n-1:-n, :]
        U[:, :, :n] = U[:, :, n:n+1]; U[:, :, -n:] = U[:, :, -n-1:-n]

def check_flux_consistency():
    rng = np.random.default_rng(0)
    for fk in (0, 1):
        for _ in range(200):
            r, u, v, p = rng.uniform(0.1, 3), rng.normal()*3, rng.normal()*3, rng.uniform(0.01, 5)
            E = p/(g-1)+0.5*r*(u*u+v*v)
            F = np.array(fv.hllc(r, u, v, p, r, u, v, p, fk))
            assert np.allclose(F, [r*u, r*u*u+p, r*u*v, u*(E+p)], rtol=1e-12, atol=1e-12), (fk, F)
    print("HLLC/HLL consistency F(U,U)=F(U): ok")

def run_sod(axis, n=200, kind=1, fk=0):
    P = Sod(axis); tag = f"sod_axis{axis}_{n}_l{kind}_f{fk}"
    fv.run(P, 1.0/n, kind, fk, tag=tag)
    d = np.load(tag + ".npz"); r = d['rho']
    prof = r[:, r.shape[1]//2] if axis == 0 else r[r.shape[0]//2, :]
    x = d['x'] if axis == 0 else d['y']
    ex = exact_sod(x, float(d['t']))
    err = np.abs(prof-ex).mean()
    # transverse invariance: the solution must not depend on the other coordinate
    spread = np.abs(r - (r[:, :1] if axis == 0 else r[:1, :])).max()
    return err, spread, prof

if __name__ == "__main__":
    check_flux_consistency()
    errs = {}
    for n in (100, 200, 400):
        e0, s0, p0 = run_sod(0, n); e1, s1, p1 = run_sod(1, n)
        print(f"Sod n={n}: L1(rho) x-sweep {e0:.3e}, y-sweep {e1:.3e}; transverse spread {s0:.1e}/{s1:.1e}; "
              f"x vs y max diff {np.abs(p0-p1).max():.1e}")
        assert abs(e0-e1) < 1e-12 and s0 < 1e-12 and s1 < 1e-12
        errs[n] = e0
    print("orders", np.log2(errs[100]/errs[200]), np.log2(errs[200]/errs[400]))
    assert errs[400] < errs[200] < errs[100]
    print("all FV checks passed")

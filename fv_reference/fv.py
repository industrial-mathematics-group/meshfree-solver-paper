"""Simple 2-D Euler finite-volume solver (gamma=1.4) for reference runs.
MUSCL reconstruction of primitive variables (MC or minmod limiter), HLLC flux,
SSP-RK3, uniform Cartesian grid, 2 ghost layers, optional solid mask (mirror cells).
Usage: python fv.py problem h [limiter] [flux]
"""
import sys, time, numpy as np
from numba import njit, prange

G = 1.4
NG = 2

@njit(inline='always')
def lim(a, b, kind):
    if a * b <= 0.0:
        return 0.0
    if kind == 0:  # minmod
        return a if abs(a) < abs(b) else b
    # MC
    s = 1.0 if a > 0 else -1.0
    return s * min(2 * abs(a), 2 * abs(b), 0.5 * abs(a + b))

@njit(inline='always')
def hllc(rL, uL, vL, pL, rR, uR, vR, pR, flux_kind):
    # normal velocity u, tangential v
    cL = np.sqrt(G * pL / rL); cR = np.sqrt(G * pR / rR)
    EL = pL / (G - 1) + 0.5 * rL * (uL * uL + vL * vL)
    ER = pR / (G - 1) + 0.5 * rR * (uR * uR + vR * vR)
    # Einfeldt / Davis estimates with Roe average
    sl = np.sqrt(rL); sr = np.sqrt(rR)
    ut = (sl * uL + sr * uR) / (sl + sr)
    HL = (EL + pL) / rL; HR = (ER + pR) / rR
    Ht = (sl * HL + sr * HR) / (sl + sr)
    vt = (sl * vL + sr * vR) / (sl + sr)
    c2 = (G - 1) * (Ht - 0.5 * (ut * ut + vt * vt))
    ct = np.sqrt(max(c2, 1e-14))
    SL = min(uL - cL, ut - ct); SR = max(uR + cR, ut + ct)
    FL0 = rL * uL; FL1 = rL * uL * uL + pL; FL2 = rL * uL * vL; FL3 = (EL + pL) * uL
    FR0 = rR * uR; FR1 = rR * uR * uR + pR; FR2 = rR * uR * vR; FR3 = (ER + pR) * uR
    if SL >= 0:
        return FL0, FL1, FL2, FL3
    if SR <= 0:
        return FR0, FR1, FR2, FR3
    if flux_kind == 1:  # HLL
        d = SR - SL
        return ((SR * FL0 - SL * FR0 + SL * SR * (rR - rL)) / d,
                (SR * FL1 - SL * FR1 + SL * SR * (rR * uR - rL * uL)) / d,
                (SR * FL2 - SL * FR2 + SL * SR * (rR * vR - rL * vL)) / d,
                (SR * FL3 - SL * FR3 + SL * SR * (ER - EL)) / d)
    SM = (pR - pL + rL * uL * (SL - uL) - rR * uR * (SR - uR)) / (rL * (SL - uL) - rR * (SR - uR))
    if SM >= 0:
        f = rL * (SL - uL) / (SL - SM)
        s0 = f; s1 = f * SM; s2 = f * vL; s3 = f * (EL / rL + (SM - uL) * (SM + pL / (rL * (SL - uL))))
        return FL0 + SL * (s0 - rL), FL1 + SL * (s1 - rL * uL), FL2 + SL * (s2 - rL * vL), FL3 + SL * (s3 - EL)
    else:
        f = rR * (SR - uR) / (SR - SM)
        s0 = f; s1 = f * SM; s2 = f * vR; s3 = f * (ER / rR + (SM - uR) * (SM + pR / (rR * (SR - uR))))
        return FR0 + SR * (s0 - rR), FR1 + SR * (s1 - rR * uR), FR2 + SR * (s2 - rR * vR), FR3 + SR * (s3 - ER)

@njit
def face(W, solid, lowo, i, j, di, dj, nrm, kind, fk):
    """face between cell (i,j) and (i+di,j+dj); stencil cells k=-1..2 along (di,dj)."""
    tng = 3 - nrm
    if solid[i, j] and solid[i + di, j + dj]:
        return 0.0, 0.0, 0.0, 0.0
    q = np.empty((4, 4))
    sol = np.zeros(4, np.bool_)
    for k in range(4):
        i0 = i + (k - 1) * di; i1 = j + (k - 1) * dj
        q[k, 0] = W[0, i0, i1]; q[k, 1] = W[nrm, i0, i1]; q[k, 2] = W[tng, i0, i1]; q[k, 3] = W[3, i0, i1]
        sol[k] = solid[i0, i1]
    if sol[2]:  # wall at face: right states are mirrors of left
        for m in range(4):
            q[2, m] = q[1, m]; q[3, m] = q[0, m]
        q[2, 1] = -q[1, 1]; q[3, 1] = -q[0, 1]
    elif sol[1]:
        for m in range(4):
            q[1, m] = q[2, m]; q[0, m] = q[3, m]
        q[1, 1] = -q[2, 1]; q[0, 1] = -q[3, 1]
    else:
        if sol[3]:
            for m in range(4):
                q[3, m] = q[2, m]
            q[3, 1] = -q[2, 1]
        if sol[0]:
            for m in range(4):
                q[0, m] = q[1, m]
            q[0, 1] = -q[1, 1]
    L = np.empty(4); R = np.empty(4)
    for m in range(4):
        dl = lim(q[1, m] - q[0, m], q[2, m] - q[1, m], kind)
        dr = lim(q[2, m] - q[1, m], q[3, m] - q[2, m], kind)
        L[m] = q[1, m] + 0.5 * dl
        R[m] = q[2, m] - 0.5 * dr
    if L[0] <= 0 or L[3] <= 0 or R[0] <= 0 or R[3] <= 0 or lowo[i, j] or lowo[i + di, j + dj]:
        for m in range(4):
            L[m] = q[1, m]; R[m] = q[2, m]
    return hllc(L[0], L[1], L[2], L[3], R[0], R[1], R[2], R[3], fk)

@njit(parallel=True)
def rhs(U, solid, lowo, h, kind, fk, out):
    nv, nx, ny = U.shape
    W = np.empty_like(U)
    for i in prange(nx):
        for j in range(ny):
            r = U[0, i, j]; u = U[1, i, j] / r; v = U[2, i, j] / r
            W[0, i, j] = r; W[1, i, j] = u; W[2, i, j] = v
            W[3, i, j] = (G - 1) * (U[3, i, j] - 0.5 * r * (u * u + v * v))
    for i in prange(nx):
        for j in range(ny):
            for m in range(4):
                out[m, i, j] = 0.0
    # x faces between i and i+1, for interior cells NG..nx-NG-1
    for j in prange(NG, ny - NG):
        for i in range(NG - 1, nx - NG):
            f0, f1, f2, f3 = face(W, solid, lowo, i, j, 1, 0, 1, kind, fk)
            # f1 normal (x) momentum, f2 tangential (y)
            out[0, i, j] -= f0 / h; out[1, i, j] -= f1 / h; out[2, i, j] -= f2 / h; out[3, i, j] -= f3 / h
            out[0, i + 1, j] += f0 / h; out[1, i + 1, j] += f1 / h; out[2, i + 1, j] += f2 / h; out[3, i + 1, j] += f3 / h
    for i in prange(NG, nx - NG):
        for j in range(NG - 1, ny - NG):
            f0, f1, f2, f3 = face(W, solid, lowo, i, j, 0, 1, 2, kind, fk)
            # f1 normal (y) momentum, f2 tangential (x)
            out[0, i, j] -= f0 / h; out[2, i, j] -= f1 / h; out[1, i, j] -= f2 / h; out[3, i, j] -= f3 / h
            out[0, i, j + 1] += f0 / h; out[2, i, j + 1] += f1 / h; out[1, i, j + 1] += f2 / h; out[3, i, j + 1] += f3 / h
    for i in prange(nx):
        for j in range(ny):
            if solid[i, j]:
                for m in range(4):
                    out[m, i, j] = 0.0

@njit(parallel=True)
def maxspeed(U, solid):
    nv, nx, ny = U.shape
    s = np.zeros(nx)
    for i in prange(NG, nx - NG):
        mx = 0.0
        for j in range(NG, ny - NG):
            if solid[i, j]:
                continue
            r = U[0, i, j]; u = U[1, i, j] / r; v = U[2, i, j] / r
            p = (G - 1) * (U[3, i, j] - 0.5 * r * (u * u + v * v))
            c = np.sqrt(G * max(p, 1e-14) / r)
            mx = max(mx, abs(u) + c, abs(v) + c)
        s[i] = mx
    return s.max()

def cons(r, u, v, p):
    return np.array([r, r * u, r * v, p / (G - 1) + 0.5 * r * (u * u + v * v)])

def prim(U):
    r = U[0]; u = U[1] / r; v = U[2] / r
    return r, u, v, (G - 1) * (U[3] - 0.5 * r * (u * u + v * v))

# ---------------- problems ----------------
class DMR:
    Lx, Ly, tend = 3.2, 1.0, 0.2
    post = cons(8.0, 8.25 * np.cos(np.pi / 6), -8.25 * np.sin(np.pi / 6), 116.5)
    pre = cons(1.4, 0.0, 0.0, 1.0)
    def xs(self, y, t):
        return 1 / 6 + (y + 20 * t) / np.sqrt(3)
    def init(self, X, Y):
        U = np.where((X < self.xs(Y, 0))[None], self.post[:, None, None], self.pre[:, None, None])
        return U
    def bc(self, U, X, Y, t):
        n = NG
        U[:, :n, :] = self.post[:, None, None]           # left inflow
        U[:, -n:, :] = U[:, -n - 1:-n, :]                 # right outflow
        # top: exact shock
        top = X[:, -n:] < self.xs(Y[:, -n:], t)
        U[:, :, -n:] = np.where(top[None], self.post[:, None, None], self.pre[:, None, None])
        # bottom
        xb = X[:, 0]
        for k in range(n):
            mir = U[:, :, 2 * n - 1 - k].copy(); mir[2] *= -1
            U[:, :, k] = np.where((xb < 1 / 6)[None], self.post[:, None], mir)

class Step:
    Lx, Ly, tend = 3.0, 1.0, 4.0
    inflow = cons(1.4, 3.0, 0.0, 1.0)
    def init(self, X, Y):
        return np.broadcast_to(self.inflow[:, None, None], (4,) + X.shape).copy()
    def solid(self, X, Y):
        return (X > 0.6) & (Y < 0.2)
    def bc(self, U, X, Y, t):
        n = NG
        U[:, :n, :] = self.inflow[:, None, None]
        U[:, -n:, :] = U[:, -n - 1:-n, :]
        for k in range(n):
            mir = U[:, :, 2 * n - 1 - k].copy(); mir[2] *= -1; U[:, :, k] = mir
            m2 = U[:, :, -2 * n + k].copy(); m2[2] *= -1; U[:, :, -1 - k] = m2

class StepFix(Step):
    """Step with a Woodward-Colella-type corner fix (my implementation): in the cells right of and above the
    corner, (i0,j0),(i0+1,j0),(i0,j0+1), the density is reset so that the entropy equals that of the
    cell left of and below the corner, (i0-1,j0-1), and the speed so that the total enthalpy equals that cell's."""
    def bc(self, U, X, Y, t):
        Step.bc(self, U, X, Y, t)
        h = X[1, 0] - X[0, 0]
        i0 = int(np.argmin(abs(X[:, 0] - (0.6 + h / 2)))); j0 = int(np.argmin(abs(Y[0, :] - (0.2 + h / 2))))
        r, u, v, p = [q[i0 - 1, j0 - 1] for q in prim(U)]
        sR = p / r**G; h0 = G / (G - 1) * p / r + 0.5 * (u * u + v * v)
        for (a, b) in ((i0, j0), (i0 + 1, j0), (i0, j0 + 1)):
            rc, uc, vc, pc = [q[a, b] for q in prim(U)]
            rn = (pc / sR)**(1 / G)
            q2 = 2 * (h0 - G / (G - 1) * pc / rn)
            sp = np.sqrt(max(q2, 0.0)); sp0 = np.hypot(uc, vc)
            un, vn = (uc * sp / sp0, vc * sp / sp0) if sp0 > 0 else (0.0, 0.0)
            U[:, a, b] = cons(rn, un, vn, pc)

class RP3:
    Lx, Ly, tend = 1.0, 1.0, 0.3
    UR = cons(1.5, 0, 0, 1.5); UL = cons(0.5323, 1.206, 0, 0.3)
    LL = cons(0.138, 1.206, 1.206, 0.029); LR = cons(0.5323, 0, 1.206, 0.3)
    s1 = -0.6633810065102821; s2 = -0.4220847070758307
    def state(self, X, Y, t):
        # exact plane-shock pattern valid near boundaries
        xa = 0.5 + self.s1 * t  # boundaries of UR (x<xa means UL at top)
        xb = 0.5 + self.s2 * t
        U = np.empty((4,) + X.shape)
        top = Y > 0.5 + self.s1 * t * 0 if False else None
        # determine quadrant by the shock positions on each side
        ur = (X > 0.5 + self.s1 * t) & (Y > 0.5 + self.s1 * t)
        ll = (X < 0.5 + self.s2 * t) & (Y < 0.5 + self.s2 * t)
        ul = (~ur) & (~ll) & (Y > 0.5 + 0.5 * (self.s1 + self.s2) * t) & (X < Y)
        lr = (~ur) & (~ll) & (~ul)
        for st, m in ((self.UR, ur), (self.LL, ll), (self.UL, ul), (self.LR, lr)):
            U[:, m] = st[:, None]
        return U
    def init(self, X, Y):
        return self.state(X, Y, 0.0)
    def bc(self, U, X, Y, t):
        n = NG
        # transmissive (zero gradient) boundaries; waves reach boundaries but stay plane
        U[:, :n, :] = U[:, n:n + 1, :]
        U[:, -n:, :] = U[:, -n - 1:-n, :]
        U[:, :, :n] = U[:, :, n:n + 1]
        U[:, :, -n:] = U[:, :, -n - 1:-n]

def bad_cells(V, solid):
    r = V[0]; p = (G - 1) * (V[3] - 0.5 * (V[1]**2 + V[2]**2) / np.where(r > 0, r, 1))
    b = ~((r > 1e-10) & (p > 1e-10) & np.isfinite(r) & np.isfinite(p)) & ~solid
    b[:NG] = False; b[-NG:] = False; b[:, :NG] = False; b[:, -NG:] = False
    return b

def stage(U0, Us, a, solid, h, kind, fk, out, dt, prob, X, Y, tb, nfix, last=False):
    lowo = np.zeros(solid.shape, np.bool_)
    for it in range(4):
        rhs(Us, solid, lowo, h, kind, fk, out)
        V = (1 - a) * U0 + a * (Us + dt * out)
        b = bad_cells(V, solid)
        if not b.any():
            break
        nfix[0] += int(b.sum())
        for k in range(it + 1):
            b = b | np.roll(b, 1, 0) | np.roll(b, -1, 0) | np.roll(b, 1, 1) | np.roll(b, -1, 1)
        lowo |= b
    else:
        raise RuntimeError('positivity fallback failed')
    prob.bc(V, X, Y, tb)
    return V

def run(prob, h, kind=1, fk=0, cfl=0.4, tag=''):
    nx = int(round(prob.Lx / h)); ny = int(round(prob.Ly / h))
    xc = (np.arange(-NG, nx + NG) + 0.5) * h; yc = (np.arange(-NG, ny + NG) + 0.5) * h
    X, Y = np.meshgrid(xc, yc, indexing='ij')
    U = prob.init(X, Y).astype(np.float64)
    solid = prob.solid(X, Y) if hasattr(prob, 'solid') else np.zeros(X.shape, bool)
    out = np.zeros_like(U)
    t = 0.0; nstep = 0; t0 = time.time(); nfix = [0]
    while t < prob.tend - 1e-12:
        prob.bc(U, X, Y, t)
        dt = cfl * h / maxspeed(U, solid)
        dt = min(dt, prob.tend - t)
        # SSP-RK3 with a-posteriori first-order fallback on faces next to non-admissible cells
        U1 = stage(U, U, 1.0, solid, h, kind, fk, out, dt, prob, X, Y, t + dt, nfix)
        U2 = stage(U, U1, 0.25, solid, h, kind, fk, out, dt, prob, X, Y, t + 0.5 * dt, nfix)
        U = stage(U, U2, 2.0 / 3.0, solid, h, kind, fk, out, dt, prob, X, Y, t + dt, nfix, last=True)
        t += dt; nstep += 1
        if nstep % 500 == 0:
            print(f'{tag} step {nstep} t={t:.4f} fixes {nfix[0]} wall {time.time()-t0:.0f}s', flush=True)
    r, u, v, p = prim(U[:, NG:-NG, NG:-NG])
    np.savez_compressed(f'{tag}.npz', rho=r, u=u, v=v, p=p, x=xc[NG:-NG], y=yc[NG:-NG], t=t,
                        solid=solid[NG:-NG, NG:-NG], h=h)
    print(f'{tag} done steps {nstep} t={t} fixes {nfix[0]} min rho {np.nanmin(np.where(solid[NG:-NG,NG:-NG],np.inf,r)):.4g} '
          f'min p {np.nanmin(np.where(solid[NG:-NG,NG:-NG],np.inf,p)):.4g} wall {time.time()-t0:.0f}s', flush=True)

if __name__ == '__main__':
    name = sys.argv[1]; n = int(sys.argv[2])
    kind = int(sys.argv[3]) if len(sys.argv) > 3 else 1
    fk = int(sys.argv[4]) if len(sys.argv) > 4 else 0
    P = {'dmr': DMR, 'step': Step, 'stepfix': StepFix, 'rp3': RP3}[name]()
    h = 1.0 / n
    import os
    if 'TEND' in os.environ: P.tend = float(os.environ['TEND'])
    run(P, h, kind, fk, tag=f'{name}_{n}_l{kind}_f{fk}' + ('_t' + os.environ['TEND'] if 'TEND' in os.environ else ''))

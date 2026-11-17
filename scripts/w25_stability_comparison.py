"""Eigenvalue test of the meshless MUSCL schemes of Willems, Klar and Samaey (2025) and of the present schemes
for 1-D linear advection (a = 1) on periodic irregular clouds.

Independent NumPy implementation (not HyperCloud or meshfree4hypeq code). Every scheme has the form
dU_i/dt = -2 sum_j c_ij (F*_ij - U_i) with Rusanov fluxes between midpoint reconstructions; they differ in
  * the reconstruction degree (no constant term, through U_i): k for "W25 MUSCLk", K-1 for "ours K",
  * the derivative weights c_ij: first-derivative row of the same fit (W25) or of a separate fit of degree q(K)
    with constant term (ours),
  * the orientation of the dissipation (geometric, or aligned for K = 1).
Least squares are solved with scaled monomials and a pseudo-inverse of sqrt(w)-scaled rows ("clean"), or as in
meshfree4hypeq ("w25": rows scaled by w, unscaled monomials, pinv with rtol = sqrt(eps); argument mode of operator).
Prints max Re(lambda) * h of the semi-discrete operator over several random clouds, for the 1-D clouds of
Willems et al. (jitter 0.5 h, radius 3.5 h, weight exp(-r^2/h^2)) and for those of the present paper
(jitter 0.2 h, radius 5.5 h, weight of Eq. (2.3)).
Run:  python3 w25_stability_comparison.py N seeds     (e.g. 100 5)
"""
import numpy as np, sys
from math import factorial
L=10.0
def grid(N, rnd, seed):
    rng=np.random.default_rng(seed); h=L/N
    x=-5+h*(np.arange(N)+0.5)+rnd*h*(2*rng.random(N)-1)
    return np.sort(x), h
def nbrs(x,h,R):
    N=len(x); out=[]
    for i in range(N):
        d=(x-x[i]+L/2)%L-L/2
        idx=np.where((np.abs(d)<=R)&(np.arange(N)!=i))[0]
        out.append((idx,d[idx]))
    return out
def wgauss(d,scale,alpha=1.0): return np.exp(-alpha*(d/scale)**2)
def wrat(d,R): y=(d/R)**2; return 1/(1+y+y*y/2+y**3/6+y**4/24)
def fit(d,w,deg,intercept,h,mode="clean"):
    """returns matrix C (deg x n): coefficient of derivative order m (row m-1) as linear map of data (differences or values)."""
    cols=[(d/h)**m/factorial(m) for m in range(1,deg+1)]
    if intercept: cols=[np.ones_like(d)]+cols
    A=np.stack(cols,1)
    if mode=="clean":
        sw=np.sqrt(w); M=np.linalg.pinv(A*sw[:,None])*sw[None,:]
    else:  # W25 code: rows scaled by w (effective weight w^2), unscaled monomials, pinv rtol sqrt(eps)
        Au=np.stack([d**m/factorial(m) for m in range(1,deg+1)],1)
        if intercept: Au=np.concatenate([np.ones((len(d),1)),Au],1)
        M=np.linalg.pinv(Au*w[:,None], rcond=np.sqrt(np.finfo(float).eps))*w[None,:]
        k0=1 if intercept else 0
        return M[k0:]
    k0=1 if intercept else 0
    return M[k0:]/ (h**np.arange(1,deg+1))[:,None]
def operator(x,h,nb,rdeg,ddeg,dint,orient,wf,mode="clean"):
    """L = -2 a sum_j c_ij (U_up - U_i), a=1. reconstruction: no-intercept fit degree rdeg through U_i.
    derivative weights: first-derivative row of fit degree ddeg (intercept dint)."""
    N=len(x); Lm=np.zeros((N,N))
    R=[];C=[]
    for i,(idx,d) in enumerate(nb):
        w=wf(d)
        if rdeg>0:
            Mr=fit(d,w,rdeg,False,h,mode)
        else: Mr=np.zeros((0,len(d)))
        R.append(Mr)
        C.append(fit(d,w,ddeg,dint,h,mode)[0])
    def recon_row(i,y):  # row vector over all particles giving R_i(y)
        r=np.zeros(N); r[i]=1.0
        idx,d=nb[i]
        for m in range(rdeg):
            coef=R[i][m]*y**(m+1)/factorial(m+1)
            r[idx]+=coef; r[i]-=coef.sum()
        return r
    for i,(idx,d) in enumerate(nb):
        for k,j in enumerate(idx):
            c=C[i][k]
            s = np.sign(c) if orient=="aligned" else np.sign(d[k])
            Uij=recon_row(i,d[k]/2); Uji=recon_row(j,-d[k]/2)
            # Rusanov a=1, s=1: F* = 1/2(Uij+Uji) - 1/2 sigma (Uji-Uij)
            F=0.5*(Uij+Uji)-0.5*s*(Uji-Uij)
            Lm[i]+=-2*c*F
            Lm[i,i]+=2*c*1.0   # minus F(U_i) term (zero row sum is not exact for no-intercept weights)
    return Lm
if __name__=="__main__":
    N=int(sys.argv[1]); seeds=int(sys.argv[2])
    cases={
     # W25 MUSCLk: recon degree k, derivative = same fit (no intercept, degree k), geometric upwind
     "W25 MUSCL1":dict(rdeg=1,ddeg=1,dint=False,orient="geo"),
     "W25 MUSCL2":dict(rdeg=2,ddeg=2,dint=False,orient="geo"),
     "W25 MUSCL3":dict(rdeg=3,ddeg=3,dint=False,orient="geo"),
     "W25 MUSCL4":dict(rdeg=4,ddeg=4,dint=False,orient="geo"),
     # ours: recon degree K-1, derivative q(K) with intercept
     "ours K=1 aligned":dict(rdeg=0,ddeg=1,dint=True,orient="aligned"),
     "ours K=1 geometric":dict(rdeg=0,ddeg=1,dint=True,orient="geo"),
     "ours K=2":dict(rdeg=1,ddeg=1,dint=True,orient="geo"),
     "ours K=3":dict(rdeg=2,ddeg=3,dint=True,orient="geo"),
     "ours K=4":dict(rdeg=3,ddeg=3,dint=True,orient="geo"),
     # hybrids
     "K=3 w/ deriv deg 2 (=W25 MUSCL2 + intercept)":dict(rdeg=2,ddeg=2,dint=True,orient="geo"),
     "K=3 deriv no intercept":dict(rdeg=2,ddeg=3,dint=False,orient="geo"),
     "W25 MUSCL1 + intercept":dict(rdeg=1,ddeg=1,dint=True,orient="geo"),
    }
    setups={"W25 setup (rnd .5h, R=3.5h, exp(-r^2/h^2))":(0.5,3.5,"g"),
            "our setup (rnd .2h, R=5.5h, rational(r/R))":(0.2,5.5,"r")}
    for sname,(rnd,kap,wk) in setups.items():
        print("==",sname,"N=",N)
        res={k:[] for k in cases}
        for s in range(seeds):
            x,h=grid(N,rnd,s); nb=nbrs(x,h,kap*h+1e-12)
            wf=(lambda d,h=h: wgauss(d,h)) if wk=="g" else (lambda d,h=h,kap=kap: wrat(d,kap*h))
            for k,c in cases.items():
                ev=np.linalg.eigvals(operator(x,h,nb,wf=wf,**c))
                res[k].append(ev.real.max()*h)
        for k,v in res.items():
            v=np.array(v); print(f"  {k:46s} max Re(lambda)*h over seeds: {v.max():+.2e}  unstable(>1e-10): {np.sum(v>1e-10)}/{len(v)}")

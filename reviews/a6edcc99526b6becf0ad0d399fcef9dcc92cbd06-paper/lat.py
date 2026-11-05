import numpy as np
from math import factorial
def run(N,k,q,kappa=2.5,orient='aligned'):
    h=1/N; x=np.arange(N)*h
    u=lambda y: 1.5+np.sin(2*np.pi*y)
    U=u(x)
    off=[o for o in range(-int(kappa),int(kappa)+1) if o!=0 and abs(o)<=kappa]
    w=lambda r: (1-r/ (kappa*h*1.0001))**2 if True else 1
    offs=np.array(off)*h; ws=np.array([(1-abs(o)/(kappa*h*1.01))**2 for o in offs])
    # deriv weights
    Pt=np.array([[o**a/factorial(a) for a in range(q+1)] for o in offs])
    Nt=(Pt*ws[:,None]).T@Pt; c=ws*(np.linalg.solve(Nt,Pt.T))[1]
    # recon fit degree k-1
    r=k-1
    if r>0:
        Pr=np.array([[o**a/factorial(a) for a in range(1,r+1)] for o in offs])
        Nr=(Pr*ws[:,None]).T@Pr; Mr=np.linalg.solve(Nr,(Pr*ws[:,None]).T)
    idx=lambda i,o: (i+o)%N
    coef=np.zeros((N,r)) if r>0 else None
    for i in range(N):
        if r>0: coef[i]=Mr@(U[[idx(i,o) for o in off]]-U[i])
    def R(i,y):
        v=U[i]
        for a in range(1,r+1): v+=coef[i,a-1]*y**a/factorial(a)
        return v
    F=lambda v: v*v/2; lam=lambda v: abs(v)
    L=np.zeros(N)
    for i in range(N):
        for jn,o in enumerate(off):
            j=idx(i,o); y=offs[jn]
            a=R(i,y/2); b=R(j,-y/2); s=max(lam(a),lam(b))
            sg=np.sign(c[jn]) if orient=='aligned' else np.sign(y)
            Fs=0.5*(F(a)+F(b))-0.5*s*sg*(b-a)
            L[i]+=-2*c[jn]*(Fs-F(U[i]))
    tau=L+U*(2*np.pi*np.cos(2*np.pi*x))
    return np.abs(tau).max()
for k,q,kap in [(1,1,1.5),(2,1,1.5),(2,1,2.5),(3,3,2.5),(4,3,3.5),(3,2,2.5)]:
  for o in ['aligned','geom']:
    e=[run(N,k,q,kap,o) for N in (40,80,160)]
    print(k,q,kap,o,['%.2e'%v for v in e],'rates',np.log2(e[0]/e[1]),np.log2(e[1]/e[2]))

"""Independent exact Riemann solution for Sod (rho,u,p)=(1,0,1)|(0.125,0,0.1), gamma=1.4, t=0.2, x0=0."""
import numpy as np
from scipy.optimize import brentq
g=1.4; rL,uL,pL=1.0,0.0,1.0; rR,uR,pR=0.125,0.0,0.1
cL=np.sqrt(g*pL/rL); cR=np.sqrt(g*pR/rR)
def f(p,r,pk,c):
    if p>pk:
        A=2/((g+1)*r); B=(g-1)/(g+1)*pk; return (p-pk)*np.sqrt(A/(p+B))
    return 2*c/(g-1)*((p/pk)**((g-1)/(2*g))-1)
ps=brentq(lambda p:f(p,rL,pL,cL)+f(p,rR,pR,cR)+uR-uL,1e-8,10)
us=0.5*(uL+uR)+0.5*(f(ps,rR,pR,cR)-f(ps,rL,pL,cL))
rsL=rL*(ps/pL)**(1/g)
rsR=rR*((ps/pR+(g-1)/(g+1))/((g-1)/(g+1)*ps/pR+1))
csL=cL*(ps/pL)**((g-1)/(2*g)); t=0.2
S=uR+cR*np.sqrt((g+1)/(2*g)*ps/pR+(g-1)/(2*g))
print(f"p*={ps:.5f} u*={us:.5f} rho*L={rsL:.5f} rho*R={rsR:.5f} head={-cL*t:.4f} tail={(us-csL)*t:.4f} contact={us*t:.4f} shock={S*t:.4f}")

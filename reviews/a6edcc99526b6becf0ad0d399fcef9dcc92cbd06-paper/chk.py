import sympy as sp, numpy as np
# Lemma lfstates
rho,s,g,p,sig=sp.symbols('rho s gamma p sigma',positive=True)
u1,u2=sp.symbols('u1 u2',real=True)
sg=sp.Symbol('sg')
E=p/(g-1)+rho*(u1**2+u2**2)/2
U=sp.Matrix([rho,rho*u1,rho*u2,E]); F=sp.Matrix([rho*u1,rho*u1*u1+p,rho*u1*u2,u1*(E+p)])
W=U-sg*F/s
th=1-sg*u1/s
ie=W[3]-(W[1]**2+W[2]**2)/(2*W[0])
claim=th*p/(g-1)-p**2/(2*th*rho*s**2)
print('lfstates diff', sp.simplify((ie-claim).subs(sg**2,1).subs(sg**3,sg)), sp.simplify((ie-claim).subs(sg,1)), sp.simplify((ie-claim).subs(sg,-1)))
# canonical forms
def canon(A,b,r):
    s=len(b); Ah=np.zeros((s+1,s+1)); Ah[:s,:s]=A; Ah[s,:s]=b
    I=np.eye(s+1); al=r*Ah@np.linalg.inv(I+r*Ah); v=(I-al)@np.ones(s+1); return al,v
def sspc(A,b):
    lo,hi=0,20
    ok=lambda r: (lambda al,v:(al>=-1e-13).all() and (v>=-1e-13).all())(*canon(A,b,r))
    if not ok(1e-9): return 0
    for _ in range(200):
        m=(lo+hi)/2
        if ok(m): lo=m
        else: hi=m
    return lo
heun=(np.array([[0,0],[1,0]]),np.array([.5,.5]))
ral=(np.array([[0,0],[2/3,0]]),np.array([.25,.75]))
rk3=(np.array([[0,0,0],[1,0,0],[.25,.25,0]]),np.array([1/6,1/6,2/3]))
rk4=(np.array([[0,0,0,0],[.5,0,0,0],[0,.5,0,0],[0,0,1,0]]),np.array([1/6,1/3,1/3,1/6]))
A=np.zeros((5,5))
A[1,0]=0.39175222700392
A[2,0]=0.21766909633821; A[2,1]=0.36841059262959
A[3,0]=0.08269208670950; A[3,1]=0.13995850206999; A[3,2]=0.25189177424738
A[4,0]=0.06796628370320; A[4,1]=0.11503469844438; A[4,2]=0.20703489864929; A[4,3]=0.54497475021237
b=np.array([0.14681187618661,0.24848290924556,0.10425883036650,0.27443890091960,0.22600748319395])
for n,(AA,bb) in dict(heun=heun,ralston=ral,rk3=rk3,rk4=rk4,ssp54=(A,b)).items():
    print(n,sspc(AA,bb))
C=sspc(A,b); al,v=canon(A,b,C)
np.set_printoptions(precision=4,suppress=True)
print(v); print(al)
al3,v3=canon(*rk3,1.0); print(v3,al3)
# eliminate W2,W4: Y3 = v2 U + a32 W2 (rows index: Y_k is row k-1)
# rows: Y3 row 2, Y5 row 4, U row 5
a=al; vv=v
W2=lambda: None
# U = v5 U + a[5,1]W2 + a[5,3]W4 + a[5,4]W5 (0-based: W_j col j-1)
c2=a[5,1]/a[2,1]; c4=a[5,3]/a[4,3]
coefU=vv[5]-c2*vv[2]-c4*vv[4]
print('elim: Y3',c2,'Y5',c4,'W5',a[5,4],'U',coefU, 'other cols', a[5,0],a[5,2], a[2,0],a[4,0],a[4,2])

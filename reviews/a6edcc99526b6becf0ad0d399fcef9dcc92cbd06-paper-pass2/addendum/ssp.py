import numpy as np
from mpmath import mp
np.set_printoptions(precision=5, suppress=True, linewidth=150)
# SSPRK(5,4) Spiteri-Ruuth in Shu-Osher form (alpha, beta), rows = stages 2..5, update
al = np.zeros((6,5)); be = np.zeros((6,5))
be[1,0]=0.391752226571890
al[2,0]=0.444370493651235; al[2,1]=0.555629506348765; be[2,1]=0.368410593050371
al[3,0]=0.620101851488403; al[3,2]=0.379898148511597; be[3,2]=0.251891774271694
al[4,0]=0.178079954393132; al[4,3]=0.821920045606868; be[4,3]=0.544974750228521
al[5,2]=0.517231671970585; al[5,3]=0.096059710526147; be[5,3]=0.063692468666290
al[5,4]=0.386708617503269; be[5,4]=0.226007483236906
al[0,:]=0
# Butcher: Y_k = U + dt sum A_kl K_l ; recursively
A=np.zeros((6,6))
for k in range(1,6):
    for j in range(5):
        A[k,:] += al[k,j]*A[j,:]
        A[k,j] += be[k,j]
def canon(A,r):
    n=A.shape[0]; I=np.eye(n)
    a=r*A@np.linalg.inv(I+r*A); v=(I-a)@np.ones(n); return a,v
def C(A):
    lo,hi=0,10
    ok=lambda r: (canon(A,r)[0]>=-1e-13).all() and (canon(A,r)[1]>=-1e-13).all()
    if not ok(1e-9): return 0
    for _ in range(200):
        m=(lo+hi)/2
        if ok(m): lo=m
        else: hi=m
    return lo
print("Butcher A (with b row):\n",A)
c=C(A); print("C(SSPRK54)=",c)
a,v=canon(A,c); print("v=",v); print("alpha=\n",a)
# elimination
v3,a32=v[2],a[2,1]; v5,a54=v[4],a[4,3]; v6=v[5]; a62,a64,a65=a[5,1],a[5,3],a[5,4]
print("other nonzeros in update row:",a[5])
print("coef Y3",a62/a32,"Y5",a64/a54,"W5",a65,"U",v6-a62*v3/a32-a64*v5/a54)
# the other methods
def mk(rows):
    s=len(rows); A=np.zeros((s,s))
    for i,r in enumerate(rows): A[i,:len(r)]=r
    return A
FE=mk([[],[1]]); RK2=mk([[],[1],[.5,.5]]); RK3=mk([[],[1],[.25,.25],[1/6,1/6,2/3]])
ral=mk([[],[2/3],[1/4,3/4]]); RK4=mk([[],[.5],[0,.5],[0,0,1],[1/6,1/3,1/3,1/6]])
for n,M in [("FE",FE),("RK2",RK2),("RK3",RK3),("Ralston",ral),("RK4",RK4)]:
    cc=C(M); print(n,"C=",cc); 
    if cc>0: a,v=canon(M,cc); print(" v",v,"\n alpha\n",a)
# check which W's enter more than one row (SSPRK54)
a,v=canon(A,c)
print("rows using each W_j:",[list(np.nonzero(np.abs(a[:,j])>1e-12)[0]+1) for j in range(5)])

import numpy as np
# Shu-Osher form of SSPRK(5,4) (Spiteri-Ruuth 2002); stages Y1=u, Y2..Y5, Y6=u^{n+1}
al=np.zeros((6,6)); be=np.zeros((6,6))
al[1,0]=1; be[1,0]=0.391752226571890
al[2,0]=0.444370493651235; al[2,1]=0.555629506348765; be[2,1]=0.368410593050371
al[3,0]=0.620101851488403; al[3,2]=0.379898148511597; be[3,2]=0.251891774271694
al[4,0]=0.178079954393132; al[4,3]=0.821920045606868; be[4,3]=0.544974750228521
al[5,2]=0.517231671970585; al[5,3]=0.096059710526147; be[5,3]=0.063692468666290
al[5,4]=0.386708617503269; be[5,4]=0.226007483236906
# Butcher: Y = e u + dt A K ; from Y_k = sum al_kj Y_j + dt be_kj K_j
I=np.eye(6); A=np.linalg.solve(I-al, be)  # coefficients of K
def canon(r):
    a=r*A@np.linalg.inv(I+r*A); v=(I-a)@np.ones(6); return a,v
lo,hi=0.5,3
for _ in range(60):
    r=(lo+hi)/2; a,v=canon(r)
    if (a>-1e-13).all() and (v>-1e-13).all(): lo=r
    else: hi=r
print('C=',lo); a,v=canon(lo)
np.set_printoptions(precision=4,suppress=True); print(v); print(a)

import numpy as np
# Shu-Osher form SSPRK(5,4) (Spiteri-Ruuth), stages u0..u4, final
a = {}
# express each stage as Butcher: Y_l = u + dt sum A_lm L(Y_m)
s=5
A=np.zeros((6,6))
# u1
A[1,0]=0.391752226571890
def comb(row_coeffs, Lterms):
    r=np.zeros(6)
    for (m,c) in row_coeffs: r+=c*A[m]
    for (m,c) in Lterms: r[m]+=c
    return r
A[2]=comb([(0,0.444370493651235),(1,0.555629506348765)],[(1,0.368410593050371)])
A[3]=comb([(0,0.620101851488403),(2,0.379898148511597)],[(2,0.251891774271694)])
A[4]=comb([(0,0.178079954393132),(3,0.821920045606868)],[(3,0.544974750228521)])
A[5]=comb([(2,0.517231671970585),(3,0.096059710526147),(4,0.386708617503269)],[(3,0.063692468666290),(4,0.226007483236906)])
print("b",A[5,:5], A[5].sum())
# order check
b=A[5,:5]; Am=A[:5,:5]; c=Am.sum(1)
print(b.sum(), b@c, b@c**2, b@Am@c)
K=A.copy()
for r in [1.508,1.5082]:
    I=np.eye(6)
    M=np.linalg.inv(I+r*K)
    alpha=r*K@M; v=M@np.ones(6)
    print(r, "v",np.round(v,3)); print(np.round(alpha,3)); print(alpha.min(), v.min())

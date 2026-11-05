import numpy as np, itertools, math
rng=np.random.default_rng(0)
# 1D neighbour counts, theta=0.4, kappa=5.5
for th,ka in [(0.4,5.5),(0.2,5.5),(0.2,5.0),(0.4,5.0)]:
    N=200000; x=np.arange(N)+rng.uniform(-th,th,N)
    cnt=np.zeros(N,int)
    for s in range(1,8):
        d=np.abs(x[s:]-x[:-s]); m=d<=ka
        cnt[s:]+=m; cnt[:-s]+=m
    c=cnt[10:-10]; print(th,ka,"min",c.min(),"frac<9",(c<9).mean(),"frac<=9",(c<=9).mean())
# 2D l1 norms of derivative weights on lattice, kappa=5.5 and 2.5, degrees 1,3
def mono(q,y):
    return np.array([y[0]**a*y[1]**(n-a)/(math.factorial(a)*math.factorial(n-a)) for n in range(q+1) for a in range(n,-1,-1)])
for ka in [2.5,5.5]:
    pts=[(i,j) for i in range(-6,7) for j in range(-6,7) if (i,j)!=(0,0) and i*i+j*j<=ka*ka]
    X=np.array(pts,float)
    w=1/np.array([sum((a*a/ka**2)**l/math.factorial(l) for l in range(5)) for a in np.linalg.norm(X,axis=1)])
    for q in [1,3]:
        P=np.array([mono(q,x) for x in X]); Nm=(P*w[:,None]).T@P
        # monomial ordering: n=1: x^1y^0 first -> index1 = d/dx
        C=np.linalg.solve(Nm,(P*w[:,None]).T)  # coeffs x data
        cx=C[1]; cy=C[2]
        l1=np.abs(cx).sum()+np.abs(cy).sum()
        print(ka,q,"l1*h",round(l1,3),"dt/h at CFL0.2, D=2:",round(0.2/(2*l1),3), "wrong sign frac", (np.sign(cx)*np.sign(X[:,0])<0).sum()/ (np.abs(X[:,0])>0).sum())

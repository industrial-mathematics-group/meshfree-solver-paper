import numpy as np, math
def weights(x,q,w=None):
    w=np.ones(len(x)) if w is None else w
    P=np.array([[xi**n/math.factorial(n) for n in range(q+1)] for xi in x])
    N=P.T@(w[:,None]*P); return w*(np.linalg.solve(N,P.T))[1]
x=np.array([-2.,-1,1,2])
c2=weights(x,2); print("q=2 weights",c2,"sum",c2.sum(),"sum c*y^3",c2@x**3,"=17/5?",17/5)
c3=weights(x,3); print("q=3 weights*12",c3*12)
# random symmetric stencil, odd q exact on degree q+1
rng=np.random.default_rng(0); y=rng.uniform(.3,2,3); xs=np.concatenate([y,-y]); w=np.exp(-xs**2)
c=weights(xs,3,w); print("q=3 on y^4:",c@xs**4, " q=3 on y^5 vs 0:",c@xs**5)

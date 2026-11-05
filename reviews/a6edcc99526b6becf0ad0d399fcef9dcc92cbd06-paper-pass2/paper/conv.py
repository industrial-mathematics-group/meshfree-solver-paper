import re,collections,math
D=collections.defaultdict(dict)
for l in open('/home/claude/meshfree-solver-paper/results/reports/2026-10-29-rerun-078-results.txt'):
    m=re.match(r'(\d+) OK\s+(\S+) MLS=(\d) N=(\S+) CFL=\S+ R=(\S+)\s+t=(\S+)/\S+\s+NaN=0\s+min\(u1\)=\S+\s+mass drift=(\S+)\s+steps=(\d+).*L1err\(u1\)=(\S+)',l)
    if not m: continue
    job,meth,mls,N,R,t,md,steps,err=m.groups()
    job=int(job)
    jit = job>=24724332
    dim = 2 if 'x' in N else 1
    n=int(N.split('x')[0])
    prob={('1','10'):'1D'}.get((str(dim),t), '2Dadv' if t=='1' else ('burg' if t=='0.5' else '1D'))
    D[(prob,meth,R,jit)][n]=(float(err),int(steps))
import json
for k in sorted(D): print(k, len(D[k]))
lat=lambda p,m,R='5.5':D[(p,m,R,False)]
per=lambda p,m,R='5.5':D[(p,m,R,True)]
# max relative diff perturbed vs lattice kappa 5.5
mx=0
for k in D:
    p,m,R,j=k
    if R=='5.5' and not j:
        q=D[(p,m,R,True)]
        for n in D[k]:
            r=q[n][0]/D[k][n][0]-1
            if abs(r)>abs(mx): mx=r; arg=(k,n)
print('max rel diff pert vs lattice k5.5',mx,arg)
for p in ['1D','2Dadv','burg']:
    for m in ['RK2MUSCL2','RK3MUSCL3','RK4SSPMUSCL4','RK4SSPMUSCL5']:
        d=lat(p,m)
        ns=sorted(d)
        print(p,m,[(n,'%.2e'%d[n][0]) for n in ns if n in (51,100,200,399,795,1000,1585,3163)])
        # mean of last 3 orders
        o=[math.log(d[a][0]/d[b][0])/math.log(b/a) for a,b in zip(ns,ns[1:])]
        print('   mean last3 %.3f'%(sum(o[-3:])/3), 'steps at 200', d.get(200,(0,0))[1])

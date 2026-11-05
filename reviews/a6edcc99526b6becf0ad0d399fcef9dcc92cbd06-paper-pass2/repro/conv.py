import re, numpy as np, sys
pat=re.compile(r"^(\d+) (OK|FAIL)\s+(RK\w+) MLS=(\d) N=(\S+) CFL=(\S+) R=(\S+)\s+t=(\S+)\s.*?steps=(\d+).*L1err\(u1\)=(\S+)")
sweeps=[]; cur=None
for line in open(sys.argv[1]):
    m=pat.match(line)
    if not m: continue
    job,st,meth,mls,N,cfl,R,t,steps,err=m.groups()
    n=int(N.split('x')[0]); key=(meth,mls,R,t,'2D' if 'x' in N else '1D')
    if cur is None or cur['key']!=key or n<=cur['N'][-1]:
        cur={'key':key,'N':[],'e':[],'jobs':set(),'st':[]}; sweeps.append(cur)
    cur['N'].append(n); cur['e'].append(float(err)); cur['jobs'].add(job); cur['st'].append(st)
for s in sweeps:
    N=np.array(s['N'],float); e=np.array(s['e'])
    o=np.log(e[:-1]/e[1:])/np.log(N[1:]/N[:-1])
    sel={k:e[list(N).index(k)] for k in (51,100,200,399,795,1000,1585,3163) if k in N}
    print(s['key'], len(N), f"Nmax={int(N[-1])} err={e[-1]:.3g} mean3={o[-3:].mean():.3f}", 'fails',s['st'].count('FAIL'), sorted(s['jobs'])[0])
    print('    ', ' '.join(f"{k}:{v:.3g}" for k,v in sel.items()))

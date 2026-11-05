import re, numpy as np
exec(open('/tmp/claude-0/-home-claude-meshfree-solver-paper/5ef34b9a-02be-5b37-bec4-3267ca618867/scratchpad/repro/conv.py').read().split('for s in sweeps')[0].replace('sys.argv[1]',"'/home/claude/meshfree-solver-paper/results/reports/2026-10-29-rerun-078-results.txt'"))
tex=open('/home/claude/meshfree-solver-paper/paper/main_light.tex').read().splitlines()[452:495]
blocks={'one-dim':'10/10','two-dimensional linear':'1/1','Burgers':'0.5/0.5'}
meths=['RK2MUSCL2','RK3MUSCL3','RK4SSPMUSCL4','RK4SSPMUSCL5']
def sweep(meth,t,R,which):
    c=[s for s in sweeps if s['key'][0]==meth and s['key'][3]==t and s['key'][2]==R]; return c[which]
cur=None
for L in tex:
    for k,v in blocks.items():
        if k in L: cur=v
    m=re.match(r'^(\d+) & (.*)\\\\',L)
    if m and cur:
        N=int(m.group(1)); cells=[c.strip() for c in m.group(2).split('&')]
        for i,me in enumerate(meths):
            s=sweep(me,cur,'5.5',0); Ns=s['N']; e=s['e']
            j=Ns.index(N); err=e[j]
            pe=float(cells[2*i].replace('e0','e+0')) if 'e' in cells[2*i] else None
            po=cells[2*i+1]
            # previous table row N
            msg=f"{cur} N={N} {me}: err {err:.3e} vs {cells[2*i]}"
            if pe and abs(err-pe)/pe>0.006: msg+="  <<ERR MISMATCH"
            if po:
                prevN=prev[cur]; jp=Ns.index(prevN); o=np.log(e[jp]/err)/np.log(N/prevN)
                msg+=f"; order {o:.3f} vs {po}"
                if abs(o-float(po))>0.0051: msg+="  <<ORDER MISMATCH"
            if 'MISMATCH' in msg: print(msg)
        prev=locals().get('prev',{}); prev[cur]=N
    m2=re.match(r'^\\multicolumn\{1\}\{l\}\{(.*?)\} & (.*)\\\\',L)
    if m2 and cur:
        lab=m2.group(1); cells=[c.strip() for c in m2.group(2).split('&')]
        for i,me in enumerate(meths):
            try:
                if lab.startswith('mean'): s=sweep(me,cur,'5.5',0)
                elif 'perturbed, $\\kappa=5.5' in lab: s=sweep(me,cur,'5.5',1)
                elif 'lattice, $\\kappa=2.5' in lab: s=sweep(me,cur,'2.5',0)
                elif 'perturbed, $\\kappa=2.5' in lab: s=sweep(me,cur,'2.5',1)
            except IndexError: continue
            N=np.array(s['N'],float); e=np.array(s['e']); o=np.log(e[:-1]/e[1:])/np.log(N[1:]/N[:-1]); m3=o[-3:].mean()
            extra=''
            if 'perturbed, $\\kappa=5.5' in lab: extra=f" ratio {e[-1]/sweep(me,cur,'5.5',0)['e'][-1]:.4f}"
            print(f"{cur} {lab} {me}: err {e[-1]:.3e} mean3 {m3:.4f}{extra} | paper {cells[2*i]} {cells[2*i+1]}")

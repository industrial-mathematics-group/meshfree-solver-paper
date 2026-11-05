import numpy as np
exec(open('/tmp/claude-0/-home-claude-meshfree-solver-paper/5ef34b9a-02be-5b37-bec4-3267ca618867/scratchpad/repro/conv2.py').read().split('cur=None')[0])
mx=0
for me in meths:
  for t in blocks.values():
    a=sweep(me,t,'5.5',0); b=sweep(me,t,'5.5',1)
    r=np.abs(np.array(b['e'])/np.array(a['e'])-1); i=r.argmax()
    print(me,t,'max rel diff pert vs lattice %.2f%% at N=%d'%(100*r[i],a['N'][i]))
for t in ('1/1','0.5/0.5'):
  for me in meths[:3]:
    a=np.array(sweep(me,t,'5.5',0)['e']); b=np.array(sweep(me,t,'2.5',0)['e']); print('lattice ratio R5.5/R2.5',me,t,'min %.1f max %.1f'%((a/b).min(),(a/b).max()))
  for me in meths[:3]:
    a=np.array(sweep(me,t,'5.5',1)['e']); b=np.array(sweep(me,t,'2.5',1)['e']); print('perturbed L1 ratio at N=1000',me,t,'%.2f'%(a[-1]/b[-1]))

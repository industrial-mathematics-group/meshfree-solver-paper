import sys; sys.path.insert(0,'/home/claude/meshfree-solver-paper/scripts')
import numpy as np, stencil_diagnostics as sd
P,L=sd.make_cloud(300,0.2,7); idx,off,m=sd.neighbour_table(P,L,2.5)
V1=np.ones(len(P)); cs={}
for q in (1,3):
    c=sd.derivative_weights(off,m,2.5,q,True); cs[q]=c
    print('q',q,'equal-vol pair defect',sd.pair_defect(idx,m,c,V1))
# without smoothing sweep: plain Shepard
W=np.where(m, sd.weight((off**2).sum(-1),2.5),0.0); S=sd.weight(0.0,2.5)+W.sum(1); V0=1/S; V0*=L*L/V0.sum()
for q in (1,3): print('q',q,'shepard no sweep', sd.pair_defect(idx,m,cs[q],V0))
rng=np.random.default_rng(8); qmix=np.where(rng.random(len(P))<0.5,1,3)
cmix=np.where((qmix==1)[:,None,None],cs[1],cs[3])
print('mixed equal vol', sd.pair_defect(idx,m,cmix,V1,mask=lambda i,j:qmix[i]!=qmix[j]))
# geometric dissipation coefficients sigma*c for degree 1: negative ones vs mean
c=cs[1]; sg=np.sign(off); coef=(sg*c)[m]  # (nentries, D)
coef=coef.ravel(); neg=coef[coef<0]
print('deg1 neg frac',len(neg)/len(coef),'most negative/mean coef', neg.min()/np.abs(coef).mean(), 'mean pos', coef[coef>0].mean())

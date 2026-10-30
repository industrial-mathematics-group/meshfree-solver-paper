import numpy as np, sys, matplotlib
from PIL import Image
lut=(matplotlib.colormaps['viridis'](np.linspace(0,1,256))[:,:3]*255)
im=np.asarray(Image.open(sys.argv[1]).convert('RGB')).astype(float)
H,W,_=im.shape
dark=(im.sum(2)<150)
def groups(a):
    g=[];s=a[0];p=a[0]
    for x in a[1:]:
        if x!=p+1: g.append((s,p)); s=x
        p=x
    g.append((s,p)); return g
rows=groups(np.where(dark.sum(1)>W*0.5)[0]); cols=groups(np.where(dark.sum(0)>H*0.3)[0])
print(rows, cols)
R=[(143,1393),(1622,2871),(3100,4350),(4578,5828)]; c0,c1=147,2958
def idx(px):
    d=((px[:,None,:]-lut[None])**2).sum(2); return d.argmin(1).astype(float)
for r0,r1 in R:
    out=[]
    for y,(a,b) in [(0.03,(2.6,3.0)),(0.2,(2.6,3.0)),(0.35,(2.6,3.0)),(0.97,(2.8,3.2))]:
        r=int(round(r0+(1-y)*(r1-r0))); px=im[r,c0+3:c1-2]; x=3.2*(np.arange(c0+3,c1-2)-c0)/(c1-c0)
        v=idx(px); m=(x>=a)&(x<=b); xs=x[m]; vs=v[m]
        # last position where value exceeds midpoint between pre-shock (right) plateau and 60th pct of left
        right=np.median(vs[-20:]); 
        k=np.where(vs>right+40)[0]; out.append(xs[k[-1]] if len(k) else np.nan)
    print("  ".join(f"{o:.3f}" for o in out))

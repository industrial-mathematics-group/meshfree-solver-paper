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
R=[(109,821),(995,1708),(1882,2594),(2768,3480)]; c0,c1=111,2249
def idx(px):
    d=((px[:,None,:]-lut[None])**2).sum(2); return d.argmin(1).astype(float)
def prof(r0,r1,y):
    r=int(round(r0+(1-y)*(r1-r0))); px=im[r,c0+3:c1-2]; x=3*(np.arange(c0+3,c1-2)-c0)/(c1-c0); return x, idx(px)
for r0,r1 in R:
    out=[]
    for y,(a,b) in [(0.05,(0.15,0.55)),(0.95,(0.3,0.9))]:
        x,v=prof(r0,r1,y); m=(x>=a)&(x<=b); xs,vs=x[m],v[m]; left=np.median(vs[:15]); right=np.median(vs[-15:]); mid=(left+right)/2
        k=np.where(vs>mid)[0]; out.append(xs[k[0]])
    x,v=prof(r0,r1,0.215); m=(x>=1.0)&(x<=1.8); xs,vs=x[m],v[m]; lo=vs[:40].min(); hi=np.median(vs[-30:]); mid=(lo+hi)/2
    k=np.where((vs>mid))[0]; out.append(xs[k[0]])
    print("  ".join(f"{o:.3f}" for o in out))
print('triple')
for r0,r1 in R:
    xs_=[]
    ys=np.arange(0.97,0.5,-0.005)
    for y in ys:
        x,v=prof(r0,r1,y); m=(x>=0.2)&(x<=0.9); xs,vs=x[m],v[m]; left=np.median(vs[:15]); 
        k=np.where(vs>left+40)[0]; xs_.append(xs[k[0]] if len(k) else np.nan)
    xs_=np.array(xs_); x0=np.median(xs_[:6]); j=np.where(np.abs(xs_-x0)>0.015)[0][0]
    print(f"stem {x0:.3f} triple y~{ys[j]:.3f} x~{xs_[j-1]:.3f}")

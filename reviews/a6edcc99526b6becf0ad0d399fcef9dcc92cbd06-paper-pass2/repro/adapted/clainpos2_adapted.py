import numpy as np, sys
from PIL import Image
import matplotlib
lut=(matplotlib.colormaps['viridis'](np.linspace(0,1,256))[:,:3]*255)
im=np.asarray(Image.open(sys.argv[1]).convert('RGB')).astype(float)
R=[(94,912),(1062,1880),(2030,2848)]; C=[(96,1119),(1221,2244)]
def idx(px):
    d=((px[:,None,:]-lut[None])**2).sum(2); return d.argmin(1).astype(float)
def cross(vals, coords, a,b,c,d):
    L=np.median(vals[(coords>=a)&(coords<=b)]); Rr=np.median(vals[(coords>=c)&(coords<=d)])
    m=(L+Rr)/2; s=np.sign(vals-m)
    k=np.where((coords>b)&(coords<c)&(np.diff(np.r_[s,s[-1]])!=0))[0]
    if len(k)==0: return np.nan
    i=k[0]; return coords[i]+(m-vals[i])/(vals[i+1]-vals[i])*(coords[i+1]-coords[i])
names=sys.argv[2].split(',')
p=0
for r0,r1 in R:
  for c0,c1 in C:
    def row(y):
        r=int(round(r0+(1-y)*(r1-r0))); px=im[r,c0+3:c1-2]; x=(np.arange(c0+3,c1-2)-c0)/(c1-c0); return idx(px),x
    def col(x):
        c=int(round(c0+x*(c1-c0))); px=im[r0+3:r1-2,c]; y=1-(np.arange(r0+3,r1-2)-r0)/(r1-r0); o=np.argsort(y); return idx(px)[o],y[o]
    out=[]
    for y in (0.05,0.15):
        v,x=row(y); out.append(cross(v,x,0.25,0.32,0.42,0.5))
    for x in (0.05,0.15):
        v,y=col(x); out.append(cross(v,y,0.25,0.32,0.42,0.5))
    v,x=row(0.9); out.append(cross(v,x,0.2,0.26,0.36,0.45))
    v,y=col(0.9); out.append(cross(v,y,0.2,0.26,0.36,0.45))
    print(f"{names[p]:28s}"+"  ".join(f"{o:.3f}" for o in out)); p+=1

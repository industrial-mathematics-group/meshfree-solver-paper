import numpy as np, sys
from PIL import Image
im=np.asarray(Image.open(sys.argv[1]).convert('RGB')).astype(float)
H,W,_=im.shape; dark=(im.sum(2)<200)
def groups(a):
    if len(a)==0: return []
    g=[];s=a[0];p=a[0]
    for x in a[1:]:
        if x!=p+1: g.append((s,p)); s=x
        p=x
    g.append((s,p)); return g
print(H,W)
print('rows', groups(np.where(dark.sum(1)>W*0.2)[0]))
print('cols', groups(np.where(dark.sum(0)>H*0.15)[0]))

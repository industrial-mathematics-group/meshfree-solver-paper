import sys, numpy as np, matplotlib; matplotlib.use('Agg'); import matplotlib.pyplot as plt
d=np.load(sys.argv[1]); r=d['rho']; x=d['x']; y=d['y']
if 'solid' in d: r=np.where(d['solid'],np.nan,r)
fig,ax=plt.subplots(figsize=(12,12*(y[-1]-y[0])/(x[-1]-x[0])+0.6))
ax.contour(x,y,r.T,30,linewidths=0.5,colors='k')
ax.set_aspect('equal'); ax.grid(True,alpha=0.4)
ax.set_xticks(np.arange(0,x[-1]+0.01,0.1),minor=True); ax.set_yticks(np.arange(0,y[-1]+0.01,0.1),minor=True)
ax.grid(True,which='minor',alpha=0.15)
if len(sys.argv)>3: ax.set_xlim(*map(float,sys.argv[3].split(','))); ax.set_ylim(*map(float,sys.argv[4].split(',')))
fig.savefig(sys.argv[2],dpi=110,bbox_inches='tight')

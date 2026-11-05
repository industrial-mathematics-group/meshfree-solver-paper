import math,re
tex=open('/home/claude/meshfree-solver-paper/paper/main_light.tex').read().splitlines()
def rows(a,b):
    out=[]
    for l in tex[a-1:b]:
        if '&' in l and re.match(r'^\d',l.strip()):
            p=[x.strip().rstrip('\\').strip() for x in l.split('&')]
            out.append(p)
    return out
def chk(a,b,ncols,name):
    R=rows(a,b)
    for c in range(ncols):
        for r0,r1 in zip(R,R[1:]):
            N0,N1=float(r0[0]),float(r1[0])
            e0,e1=float(r0[1+2*c].replace('e0','e+0') if 'e0'==r0[1+2*c][-3:-1] else r0[1+2*c]),float(r1[1+2*c])
            o=math.log(e0/e1)/math.log(N1/N0)
            stated=r1[2+2*c]
            if abs(o-float(stated))>0.015: print(name,'col',c,'N',N1,'computed %.3f stated %s'%(o,stated))
chk(459,464,4,'1D'); chk(471,476,4,'2Dadv'); chk(483,488,4,'burg'); chk(528,534,3,'vortex')

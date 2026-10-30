import numpy as np, sys, os
from scipy.optimize import fsolve
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
exec(open(os.path.join(os.path.dirname(os.path.abspath(__file__)),'tst.py')).read().split('Ms=10.0')[0])
Ms=10.0; thw=np.radians(30)
def solve(chi):
    phi1=np.pi/2-thw-chi; M0=Ms/np.sin(phi1)
    p1,th1,M1,r1=oblique(M0,phi1)
    def e(v):
        phi2,phi3=v
        p2,th2,_,_=oblique(M1,phi2); p3,th3,_,_=oblique(M0,phi3)
        return [p1*p2-p3, th1-th2-th3]
    phi2,phi3=fsolve(e,(0.77,1.4))
    p2,th2,M2,r2=oblique(M1,phi2); p3,th3,M3,r3=oblique(M0,phi3)
    # orientation in wall frame: incoming flow direction is along the triple-point path (angle chi), flowing towards -path.
    # stem angle w.r.t. wall: flow direction angle (chi+180); stem makes angle phi3 with flow -> stem line angle to wall = 180 - (phi3 - chi)?? report phi3+chi
    return np.degrees([phi2,phi3,th1,th2,th3]), p3, r1*r2*1.4, r3*1.4
for c in [7.73,9.0,10.0,11.0]:
    ang,p3,rho2,rho3=solve(np.radians(c))
    print(f'chi={c}: phi2={ang[0]:.2f} phi3={ang[1]:.2f} -> stem angle to wall at T = {ang[1]+c:.2f} deg; th1={ang[2]:.2f} th2={ang[3]:.2f}; p behind stem {p3:.1f}; rho2={rho2:.2f} rho3={rho3:.2f}')
d=np.loadtxt('dmr_240_l1_f0_front.txt'); y,xf=d[:,0],d[:,1]
for y0 in [0.36,0.38,0.40,0.42]:
    m=(y>y0-0.02)&(y<y0+0.02); s=np.polyfit(y[m],xf[m],1)[0]
    print(f'numerical stem at y={y0}: dx/dy={s:.3f} -> angle to wall {np.degrees(np.arctan2(1,s)):.2f} deg')

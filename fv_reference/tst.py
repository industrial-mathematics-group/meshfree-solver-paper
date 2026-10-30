import numpy as np
from scipy.optimize import fsolve, brentq
g=1.4
def oblique(M,phi):
    # returns p ratio, deflection, downstream Mach, rho ratio
    Mn=M*np.sin(phi)
    pr=1+2*g/(g+1)*(Mn**2-1)
    rr=(g+1)*Mn**2/((g-1)*Mn**2+2)
    th=np.arctan(2/np.tan(phi)*(Mn**2-1)/(M**2*(g+np.cos(2*phi))+2))
    Mn2=np.sqrt((1+(g-1)/2*Mn**2)/(g*Mn**2-(g-1)/2))
    M2=Mn2/np.sin(phi-th)
    return pr,th,M2,rr
Ms=10.0; thw=np.radians(30)  # shock at 60 deg to wall
print("top intersection exact x =",1/6+(1+4)/np.sqrt(3))
def eqs(v):
    chi,phi2=v
    phi1=np.pi/2-thw-chi
    M0=Ms/np.sin(phi1)
    p1,th1,M1,r1=oblique(M0,phi1)
    p2,th2,M2,r2=oblique(M1,phi2)
    phi3=np.pi/2-chi
    p3,th3,M3,r3=oblique(M0,phi3)
    return [p1*p2-p3, th1-th2-th3]
for guess in [(0.1,0.6),(0.2,0.5),(0.05,0.8)]:
    sol,info,ier,msg=fsolve(eqs,guess,full_output=True)
    print(np.degrees(sol),ier,eqs(sol))
chi,phi2=fsolve(eqs,(0.1,0.6))
t=0.2
s=20*t/(np.sqrt(3)-np.tan(chi))
print("chi deg",np.degrees(chi),"triple point x",1/6+s,"y",s*np.tan(chi))
# also details
phi1=np.pi/2-thw-chi;M0=Ms/np.sin(phi1)
print("M0 in TP frame",M0,"phi1",np.degrees(phi1),"oblique1",oblique(M0,phi1))
p1,th1,M1,r1=oblique(M0,phi1);print("reflected",np.degrees(phi2),oblique(M1,phi2))
print("stem",oblique(M0,np.pi/2-chi))

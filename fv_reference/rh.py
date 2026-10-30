import numpy as np
g=1.4
def speed(L,R):  # 1D states (rho,u,p) normal velocity; shock speed by mass flux
    rl,ul,pl=L; rr,ur,pr=R
    s=(rl*ul-rr*ur)/(rl-rr)
    # check momentum
    mom=(rl*ul**2+pl-rr*ur**2-pr)/(rl*ul-rr*ur)
    El=pl/(g-1)+.5*rl*ul**2; Er=pr/(g-1)+.5*rr*ur**2
    en=((El+pl)*ul-(Er+pr)*ur)/(El-Er)
    return s,mom,en
# UL (0.5323,1.206,0,0.3) | UR (1.5,0,0,1.5): x-direction
print("UL|UR",speed((0.5323,1.206,0.3),(1.5,0,1.5)))
print("LL|LR",speed((0.138,1.206,0.029),(0.5323,0,0.3)))
for s in [speed((0.5323,1.206,0.3),(1.5,0,1.5))[0],speed((0.138,1.206,0.029),(0.5323,0,0.3))[0]]:
    print("pos at t=0.3:",0.5+s*0.3)

"""Euler helpers (flux, wave speed, conserved variables, pressure; gamma = 1.4) shared by the Monte Carlo scripts."""
import numpy as np
g = 1.4
def flux(U, d):
    r, mx, my, E = U; u, v = mx/r, my/r; p = (g-1)*(E-0.5*r*(u*u+v*v)); vel = (u, v)[d]
    return np.array([r*vel, mx*vel + (p if d == 0 else 0), my*vel + (p if d == 1 else 0), vel*(E+p)])
def lam(U, d):
    r, mx, my, E = U; u, v = mx/r, my/r; p = (g-1)*(E-0.5*r*(u*u+v*v)); return abs((u, v)[d]) + np.sqrt(g*p/r)
def cons(r, u, v, p): return np.array([r, r*u, r*v, p/(g-1)+0.5*r*(u*u+v*v)])
def pres(U): r, mx, my, E = U; return (g-1)*(E-0.5*(mx*mx+my*my)/r)

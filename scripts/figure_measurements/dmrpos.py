"""Mach stem and incident shock of the double Mach reflection from paper/figures/dmr_density_078.jpg.

Usage: python dmrpos.py ../../paper/figures/dmr_density_078.jpg
Prints per panel (top to bottom) the x position of the last point behind the front (colour index
more than 40 above the pre-shock plateau on the right) at y=0.03, 0.2, 0.35 (Mach stem) and at
y=0.97 (incident shock near the top boundary). Plotted domain [0,3.2]x[0,1].
"""
import sys
import numpy as np
from frames import load, colour_index, panels

im = load(sys.argv[1])
R, C = panels(im, aspect=3.0)
c0, c1 = C[0]
print('panels', R, C)
print('y=0.03  y=0.2  y=0.35  y=0.97')
for r0, r1 in R:
    out = []
    for y, (a, b) in [(0.03, (2.6, 3.0)), (0.2, (2.6, 3.0)), (0.35, (2.6, 3.0)), (0.97, (2.8, 3.2))]:
        r = int(round(r0 + (1 - y) * (r1 - r0))); px = im[r, c0 + 3:c1 - 2]
        x = 3.2 * (np.arange(c0 + 3, c1 - 2) - c0) / (c1 - c0)
        v = colour_index(px); m = (x >= a) & (x <= b); xs = x[m]; vs = v[m]
        right = np.median(vs[-20:])
        k = np.where(vs > right + 40)[0]
        out.append(xs[k[-1]] if len(k) else np.nan)
    print('  '.join(f'{o:.3f}' for o in out))

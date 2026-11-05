"""Plane-shock positions of the 2-D Riemann problem from paper/figures/riemann2d_density_078.jpg.

Usage: python clainpos2.py ../../paper/figures/riemann2d_density_078.jpg [name1,name2,...]
Panels are read row by row, left to right. For each panel the script prints the crossing of the
mid level between the two plateaus along the rows y=0.05, 0.15 and the columns x=0.05, 0.15
(the two plane shocks near the boundaries, exact 0.301 and 0.373), and along y=0.9 and x=0.9.
"""
import sys
import numpy as np
from frames import load, colour_index, panels

im = load(sys.argv[1])
R, C = panels(im, aspect=1.25)
print('panels', R, C)
names = sys.argv[2].split(',') if len(sys.argv) > 2 else [f'panel{i+1}' for i in range(len(R) * len(C))]


def cross(vals, coords, a, b, c, d):
    L = np.median(vals[(coords >= a) & (coords <= b)]); Rr = np.median(vals[(coords >= c) & (coords <= d)])
    m = (L + Rr) / 2; s = np.sign(vals - m)
    k = np.where((coords > b) & (coords < c) & (np.diff(np.r_[s, s[-1]]) != 0))[0]
    if len(k) == 0:
        return np.nan
    i = k[0]
    return coords[i] + (m - vals[i]) / (vals[i + 1] - vals[i]) * (coords[i + 1] - coords[i])


print(f"{'':28s}y=0.05 y=0.15 x=0.05 x=0.15 y=0.9  x=0.9")
p = 0
for r0, r1 in R:
    for c0, c1 in C:
        def row(y):
            r = int(round(r0 + (1 - y) * (r1 - r0))); px = im[r, c0 + 3:c1 - 2]
            x = (np.arange(c0 + 3, c1 - 2) - c0) / (c1 - c0); return colour_index(px), x

        def col(x):
            c = int(round(c0 + x * (c1 - c0))); px = im[r0 + 3:r1 - 2, c]
            y = 1 - (np.arange(r0 + 3, r1 - 2) - r0) / (r1 - r0); o = np.argsort(y)
            return colour_index(px)[o], y[o]
        out = []
        for y in (0.05, 0.15):
            v, x = row(y); out.append(cross(v, x, 0.25, 0.32, 0.42, 0.5))
        for x in (0.05, 0.15):
            v, y = col(x); out.append(cross(v, y, 0.25, 0.32, 0.42, 0.5))
        v, x = row(0.9); out.append(cross(v, x, 0.2, 0.26, 0.36, 0.45))
        v, y = col(0.9); out.append(cross(v, y, 0.2, 0.26, 0.36, 0.45))
        print(f'{names[p] if p < len(names) else p:28s}' + '  '.join(f'{o:.3f}' for o in out)); p += 1

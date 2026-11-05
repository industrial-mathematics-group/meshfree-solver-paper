"""Wave positions of the Mach 3 step runs from paper/figures/mach3_density_078.jpg (Table tab:steppos).

Usage: python steppos.py ../../paper/figures/mach3_density_078.jpg
Prints per panel (top to bottom): bow shock at y=0.05, Mach stem at y=0.95, reflection on the
step at y=0.215; then the stem position and the triple point. Domain [0,3]x[0,1].
"""
import sys
import numpy as np
from frames import load, colour_index, panels

im = load(sys.argv[1])
R, C = panels(im, aspect=3.0)
c0, c1 = C[0]
print('panels', R, C)


def prof(r0, r1, y):
    r = int(round(r0 + (1 - y) * (r1 - r0)))
    px = im[r, c0 + 3:c1 - 2]
    x = 3 * (np.arange(c0 + 3, c1 - 2) - c0) / (c1 - c0)
    return x, colour_index(px)


def first(k, xs):
    return xs[k[0]] if len(k) else np.nan


print('bow(y=0.05)  stem(y=0.95)  reflection(y=0.215)')
for r0, r1 in R:
    out = []
    for y, (a, b) in [(0.05, (0.15, 0.55)), (0.95, (0.3, 0.9))]:
        x, v = prof(r0, r1, y); m = (x >= a) & (x <= b); xs, vs = x[m], v[m]
        mid = (np.median(vs[:15]) + np.median(vs[-15:])) / 2
        out.append(first(np.where(vs > mid)[0], xs))
    x, v = prof(r0, r1, 0.215); m = (x >= 1.0) & (x <= 1.8); xs, vs = x[m], v[m]
    mid = (vs[:40].min() + np.median(vs[-30:])) / 2
    out.append(first(np.where(vs > mid)[0], xs))
    print('  '.join(f'{o:.4f}' for o in out))
print('triple point')
for r0, r1 in R:
    xs_ = []
    ys = np.arange(0.97, 0.5, -0.005)
    for y in ys:
        x, v = prof(r0, r1, y); m = (x >= 0.2) & (x <= 0.9); xs, vs = x[m], v[m]
        xs_.append(first(np.where(vs > np.median(vs[:15]) + 40)[0], xs))
    xs_ = np.array(xs_); x0 = np.median(xs_[:6])
    j = np.where(np.abs(xs_ - x0) > 0.015)[0]
    if len(j):
        print(f'stem {x0:.3f} triple y~{ys[j[0]]:.3f} x~{xs_[j[0]-1]:.3f}')
    else:
        print(f'stem {x0:.3f} (no triple point found)')

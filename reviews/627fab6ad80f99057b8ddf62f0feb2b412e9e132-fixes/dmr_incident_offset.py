"""Incident shock of the DMR figure against the exact line x = 1/6 + (y + 20 t)/sqrt(3), t = 0.2.
Uses the panel detection of scripts/figure_measurements/frames.py and a half-jump criterion.
Run from the repository root: python3 reviews/627fab6ad80f99057b8ddf62f0feb2b412e9e132-fixes/dmr_incident_offset.py"""
import os, sys
import numpy as np
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'scripts', 'figure_measurements'))
from frames import load, colour_index, panels

im = load('paper/figures/dmr_density_078.jpg')
R, C = panels(im, 3.0)
c0, c1 = C[0]
for y in (0.97, 0.9, 0.8):
    out = []
    for r0, r1 in R:
        r = int(round(r0 + (1 - y) * (r1 - r0)))
        px = im[r, c0 + 3:c1 - 2]
        x = 3.2 * (np.arange(c0 + 3, c1 - 2) - c0) / (c1 - c0)
        v = colour_index(px)
        m = (x >= 2.6) & (x <= 3.2); xs, vs = x[m], v[m]
        right = np.median(vs[-15:]); left = np.median(vs[xs < xs[0] + 0.05])
        out.append(xs[np.where(vs > (left + right) / 2)[0][-1]])
    print(f'y={y}: exact {1/6 + (y + 4) / np.sqrt(3):.3f}, panels', ' '.join(f'{o:.3f}' for o in out))

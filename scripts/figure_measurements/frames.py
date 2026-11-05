"""Panel detection for the PDEStudio colour-map exports in paper/figures/*.jpg.

The panels are framed by dark lines. A frame line is a pixel row (column) in which more than
half (30 %) of the pixels are dark. Columns: consecutive frame lines at least W/4 apart form the
left and right edges of a panel column. Rows: two frame lines form the top and bottom of a panel
if their distance is the panel width divided by the plot aspect ratio (plot_width/plot_height in
the export metadata, results/configs/*/*.csv) to within 2 %. Lines inside a panel (such as the
outline of the step) are skipped this way. Positions are the centres of the line groups.
"""
import numpy as np
import matplotlib
from PIL import Image

LUT = matplotlib.colormaps['viridis'](np.linspace(0, 1, 256))[:, :3] * 255


def load(path):
    return np.asarray(Image.open(path).convert('RGB')).astype(float)


def colour_index(px):
    """Index 0..255 of the nearest viridis colour for an (n, 3) array of RGB pixels."""
    d = ((px[:, None, :] - LUT[None]) ** 2).sum(2)
    return d.argmin(1).astype(float)


def _groups(a):
    g = []; s = a[0]; p = a[0]
    for x in a[1:]:
        if x != p + 1:
            g.append((s + p) / 2); s = x
        p = x
    g.append((s + p) / 2)
    return [int(round(x)) for x in g]


def panels(im, aspect):
    """Return (rows, cols): lists of (top, bottom) and (left, right) pixel edges of the panels."""
    H, W, _ = im.shape
    dark = im.sum(2) < 150
    rl = _groups(np.where(dark.sum(1) > W * 0.5)[0])
    cl = _groups(np.where(dark.sum(0) > H * 0.3)[0])
    cols = []; i = 0
    while i + 1 < len(cl):
        if cl[i + 1] - cl[i] > W / 4:
            cols.append((cl[i], cl[i + 1])); i += 2
        else:
            i += 1
    if not cols:
        raise SystemExit('no panel columns found')
    h = (cols[0][1] - cols[0][0]) / aspect
    rows = []; i = 0
    while i < len(rl):
        j = next((j for j in range(i + 1, len(rl)) if abs(rl[j] - rl[i] - h) < 0.02 * h), None)
        if j is None:
            i += 1
        else:
            rows.append((rl[i], rl[j])); i = j + 1
    if not rows:
        raise SystemExit('no panel rows found')
    return rows, cols

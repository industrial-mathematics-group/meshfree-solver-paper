import sys, numpy as np
def crossing(x, f, i0, i1, nback=6):
    """jump located between indices i0 (one side) and i1 (other side, i1>i0 or <): plateau
    values taken nback cells outside the steepest gradient; return x where f crosses mean."""
    lo, hi = min(i0, i1), max(i0, i1)
    k = lo + np.argmax(np.abs(np.diff(f[lo:hi + 1])))  # steepest between k,k+1
    a = f[max(k - nback, 0)]; b = f[min(k + 1 + nback, len(f) - 1)]
    m = 0.5 * (a + b)
    # search near k for crossing of m
    for q in range(max(k - nback, 0), min(k + nback, len(f) - 2) + 1):
        if (f[q] - m) * (f[q + 1] - m) <= 0 and f[q] != f[q + 1]:
            if abs(q - k) <= nback:
                return x[q] + (m - f[q]) / (f[q + 1] - f[q]) * (x[q + 1] - x[q]), a, b
    return np.nan, a, b
def leading_front_from_right(x, f, pre, tol=0.05):
    idx = np.where(np.abs(f - pre) > tol * pre)[0]
    i = idx.max()
    return crossing(x, f, i - 8, min(i + 4, len(f) - 1))
def leading_front_from_left(x, f, pre, tol=0.05, start=0):
    idx = np.where(np.abs(f[start:] - pre) > tol * pre)[0] + start
    i = idx.min()
    return crossing(x, f, max(i - 4, 0), i + 8)

def dmr(fn):
    d = np.load(fn); r = d['rho']; x = d['x']; y = d['y']; t = float(d['t']); h = float(d['h'])
    xs = lambda yy: 1/6 + (yy + 20*t)/np.sqrt(3)
    xf = np.array([leading_front_from_right(x, r[:, j], 1.4)[0] for j in range(len(y))])
    dev = xf - xs(y)
    print(f'{fn}: h=1/{round(1/h)}  t={t}')
    print('  Mach stem foot at wall (y=h/2): x = %.4f' % xf[0], ' plateaus', leading_front_from_right(x, r[:, 0], 1.4)[1:])
    for yy in [0.05, 0.1, 0.2, 0.3]:
        j = np.argmin(abs(y - yy)); print('  leading front at y=%.3f: x=%.4f (incident line %.4f)' % (y[j], xf[j], xs(y[j])))
    # top
    print('  incident shock at top row y=%.4f: x=%.4f exact %.4f' % (y[-1], xf[-1], xs(y[-1])))
    # triple point: highest y where deviation > 2h (and above that the front is on incident line)
    ok = np.abs(dev) < 1.0*h
    # topmost y index below which deviation exceeds 2h
    above = np.where(dev > 2*h)[0]
    jT = above.max()
    for thr in [1, 2, 3]:
        jj = np.where(dev > thr*h)[0].max()
        print(f'  triple point (front departs incident line by >{thr}h): y={y[jj]:.4f}, x_inc={xs(y[jj]):.4f}, x_front={xf[jj]:.4f}')
    yT = y[jT]; xT = xs(yT)
    print('  triple point path angle chi = %.2f deg (from (1/6,0))' % np.degrees(np.arctan2(yT, xT - 1/6)))
    np.savetxt(fn.replace('.npz', '_front.txt'), np.c_[y, xf, xs(y)], fmt='%.5f', header='y x_front x_incident')
def step(fn):
    d = np.load(fn); r = d['rho']; x = d['x']; y = d['y']; h = float(d['h'])
    r = np.where(d['solid'], np.nan, r)
    print(f'{fn}: h=1/{round(1/h)}')
    for yy in [0.05, 0.1, 0.15, 0.95, 0.9, 0.85]:
        j = np.argmin(abs(y - yy)); xx, a, b = leading_front_from_left(x, r[:, j], 1.4)
        print(f'  leading shock at y={y[j]:.4f}: x={xx:.4f}  plateaus {a:.3f} {b:.3f}')
    # triple point: leading front vs y in upper half
    xf = np.array([leading_front_from_left(x, r[:, j], 1.4)[0] for j in range(len(y))])
    jt = np.argmin(abs(y - 0.95)); xstem = xf[jt]
    dev = np.abs(xf - xstem)
    ys = y[(y > 0.4) & (dev > 2*h)]
    print('  triple point (front departs from stem x by >2h): y=%.4f' % ys.max())
    ys3 = y[(y > 0.4) & (dev > 4*h)]; print('   (>4h): y=%.4f' % ys3.max())
    # reflection on step at y=0.215 (or nearest row above step), x in [0.9, 2.0]
    for yy in [0.205, 0.215, 0.225]:
        j = np.argmin(abs(y - yy)); f = r[:, j]
        i0 = np.searchsorted(x, 0.95); i1 = np.searchsorted(x, 1.8)
        k = i0 + np.argmax(np.abs(np.diff(f[i0:i1])))
        xx, a, b = crossing(x, f, k - 3, k + 4)
        print(f'  strongest jump on y={y[j]:.4f} in [0.95,1.8]: x={xx:.4f} plateaus {a:.3f} {b:.3f}')
    np.savetxt(fn.replace('.npz', '_front.txt'), np.c_[y, xf], fmt='%.5f', header='y x_leadingfront')
if __name__ == '__main__':
    {'dmr': dmr, 'step': step}[sys.argv[1]](sys.argv[2])

def dmr2(fn):
    d = np.load(fn); r = d['rho']; x = d['x']; y = d['y']; t = float(d['t']); h = float(d['h'])
    xs = lambda yy: 1/6 + (yy + 20*t)/np.sqrt(3)
    S = lambda X: 1/6 + (X - 1/6)*t/0.2
    xf = np.array([leading_front_from_right(x, r[:, j], 1.4)[0] for j in range(len(y))])
    dev = xf - xs(y)
    jd = np.where(dev > 2*h)[0].max()
    # fit stem x(y) (quadratic) on y in [yd-0.12, yd-0.02] and intersect with incident line
    m = (y > y[jd] - 0.12*t/0.2) & (y < y[jd] - 0.02*t/0.2)
    c = np.polyfit(y[m], xf[m], 2)
    yy = np.linspace(y[jd] - 0.05*t/0.2, y[jd] + 0.08*t/0.2, 20001)
    k = np.argmin(abs(np.polyval(c, yy) - xs(yy)))
    yT = yy[k]; xT = xs(yT)
    print(f'{fn}: triple point by stem-fit/incident intersection: x={xT:.4f}, y={yT:.4f}, chi={np.degrees(np.arctan2(yT, xT-1/6)):.2f} deg')
    # reflected shock: scan columns from top, first departure from rho=8 below the incident shock
    xr = []; yr = []
    for i in range(len(x)):
        if x[i] < S(1.6) or x[i] > xT - 0.02*t/0.2: continue
        col = r[i, ::-1]; yc = y[::-1]
        # start below the incident shock
        jstart = np.where(xs(yc) > x[i] + 0.02*t/0.2)[0]
        if len(jstart) == 0: continue
        j0 = jstart[0]
        idx = np.where(np.abs(col[j0:] - 8.0) > 0.05*8.0)[0]
        if len(idx) == 0: continue
        j = j0 + idx[0]
        xr.append(x[i]); yr.append(yc[j] + 0.5*h)
    xr = np.array(xr); yr = np.array(yr)
    np.savetxt(fn.replace('.npz', '_reflected.txt'), np.c_[xr, yr], fmt='%.5f')
    # kink: lines fitted to the straight reflected-shock segment right of the kink and to the part left of it
    A = (xr > S(2.32)) & (xr < xT - 0.06*t/0.2); B = (xr > S(2.0)) & (xr < S(2.15))
    pb = np.polyfit(xr[A], yr[A], 1); pa = np.polyfit(xr[B], yr[B], 1)
    xi = (pb[1] - pa[1]) / (pa[0] - pb[0]); yi = np.polyval(pa, xi)
    W = (xr > S(2.0)) & (xr < S(2.5)); jmin = np.argmin(yr[W]); xm = xr[W][jmin]; ym = yr[W][jmin]
    print(f'   kink of reflected shock: line intersection x={xi:.4f}, y={yi:.4f} (slopes {pa[0]:.3f} left, {pb[0]:.3f} right); lowest point of reflected shock x={xm:.4f}, y={ym:.4f}')
    print(f'   Mach stem: x at wall {xf[0]:.4f}; at y=0.1 {xf[np.argmin(abs(y-0.1*t/0.2))]:.4f}; at y=0.3 {xf[np.argmin(abs(y-0.3*t/0.2))]:.4f} (y scaled with t/0.2)')
    sc = lambda X, Y: ((X - 1/6)/t, Y/t)
    print('   similarity coords (xi=(x-1/6)/t, eta=y/t): foot xi=%.3f; T (%.3f, %.3f); kink (%.3f, %.3f)' % (sc(xf[0],0)[0], *sc(xT,yT), *sc(xi,yi)))

def rp3(fn):
    d = np.load(fn); r = d['rho']; x = d['x']; y = d['y']; h = float(d['h'])
    print(f'{fn}: h=1/{round(1/h)}')
    # plane shocks far from centre
    j = np.argmin(abs(y - 0.8)); print('  UR shock at y=0.8: x=%.4f (RH 0.3010)' % leading_front_from_left(x, r[:, j], 0.5323)[0])
    i = np.argmin(abs(x - 0.1)); print('  LL shock at x=0.1: y=%.4f (RH 0.3734)' % leading_front_from_left(y, r[i, :], 0.138)[0])
    # LL-shock triple point: columns from bottom, front of 0.138 state
    yf = np.array([leading_front_from_left(y, r[i, :], 0.138)[0] if x[i] < 0.37 else np.nan for i in range(len(x))])
    dev = 0.37337 - yf
    xt = x[(x < 0.37) & (dev < 2*h)].max()
    print('  lower-left triple point (front leaves y=0.373 by >2h): x=%.4f (mirror: y=%.4f)' % (xt, xt))
    # curved shock on diagonal
    dg = np.diag(r); s = x
    print('  curved shock on diagonal: x=y=%.4f' % leading_front_from_left(s, dg, 0.138)[0])
    # UR-shock triple point: rows from left; UL state 0.5323 then shock at 0.301
    xf = np.array([leading_front_from_left(x, r[:, j], 0.5323)[0] if y[j] > 0.38 else np.nan for j in range(len(y))])
    yt = y[(y > 0.38) & (np.abs(xf - 0.30099) < 2*h)].min()
    print('  upper triple point on UR shock (lowest y where front at x=0.301 within 2h): y=%.4f (mirror x)' % yt)
    k = np.argmax(np.where(np.isnan(dg), -1, dg)); print('  max density %.4f at x=y=%.4f; global max %.4f' % (dg[k], s[k], r.max()))
    # density along diagonal coarse print for jet features
    np.savetxt(fn.replace('.npz', '_diag.txt'), np.c_[s, dg], fmt='%.5f', header='s rho(s,s)')

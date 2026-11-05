"""Check: ho_common.bloch_symbols infers h = 1/(3*round(N0**(1/D))). For 1-D merge/insert defect cells N0 = m-1 / m+1,
so h (and the support radius R = kappa*h) differ from the lattice spacing 1/(3m). Compare against a version with the
correct h (= 1/(3m))."""
import sys
sys.path.insert(0, sys.argv[1])
import numpy as np
import ho_common as hc
from linop import build_operator, neighbours

def bloch_fixed_h(P0, m, kappa, K, a, orient, thetas, copies=3):
    N0, D = P0.shape
    h = 1.0 / (copies * m)
    P, shifts = hc.supercell_cloud(P0, copies)
    mid = (copies - 1) // 2
    kmid = int(np.where((shifts == mid).all(1))[0][0])
    L = build_operator(P, h, kappa, K, a, orient)
    rows = L[kmid * N0:(kmid + 1) * N0, :]
    out = []
    for th in thetas:
        ph = np.exp(1j * (shifts - mid) @ np.atleast_1d(th))
        S = sum(rows[:, b*N0:(b+1)*N0] * ph[b] for b in range(len(shifts)))
        out.append(S)
    return out, h

if __name__ == "__main__":
    for typ in ("merge", "insert"):
      for m in (8, 16):
          g = (np.arange(m) + 0.5) / m
          if typ == "merge":
              g = np.delete(g, m // 2)
          else:
              g = np.sort(np.append(g, (m // 2 + 1.0) / m))
          P0 = g[:, None]
          th = np.linspace(-np.pi, np.pi, 64, endpoint=False)
          for K in (2, 3):
              s1, h1 = hc.bloch_symbols(P0, 2.5, K, [1.0], "geometric", th)
              s2, h2 = bloch_fixed_h(P0, m, 2.5, K, [1.0], "geometric", th)
              a1 = max(np.linalg.eigvals(S).real.max() for S in s1) * h1
              a2 = max(np.linalg.eigvals(S).real.max() for S in s2) * h2
              # neighbour radius in lattice spacings
              print(f"{typ} m={m} K={K}: script h={h1:.5f} (R/spacing={2.5*h1*3*m:.3f}) alpha_h={a1:.3e} | correct h={h2:.5f} alpha_h={a2:.3e}"
                    f" | max|S_script-S_fixed|={max(np.abs(x - y).max() for x, y in zip(s1, s2)):.2e}")

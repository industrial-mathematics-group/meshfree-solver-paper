"""Recompute Table tab:euler2d of paper/main_light.tex (min p and final mass relative to RK2MUSCL2(EPD1,AR,MLS2))
from the Euler-shock rows of results/reports/2026-10-29-rerun-078-tables.md. The 'mass change' column there is the
relative drift m(T)/m(0) - 1, so the final mass relative to the reference is (1+d)/(1+d_ref) - 1."""
import sys
R = sys.argv[1]
tab = open(f"{R}/2026-10-29-rerun-078-tables.md").read().split("## Euler shock problems")[1].split("## Isentropic")[0]
rows = {}
for row in tab.splitlines():
    c = [x.strip() for x in row.strip("|").split("|")]
    if len(c) < 13 or not c[12].isdigit(): continue
    rows[(c[0], c[3].split()[0])] = (c[1], float(c[8]), float(c[9]))
for prob in ("Mach3Step", "DMR", "clainshock"):
    ref = rows[(prob, "k2.epd1.ar.mls2")][2]
    print(prob)
    for (p, key), (grid, mp, d) in sorted(rows.items()):
        if p != prob: continue
        print(f"   {key:18s} {grid:9s} min p {mp:.2g}  mass {100*((1+d)/(1+ref)-1):+.1f}%")

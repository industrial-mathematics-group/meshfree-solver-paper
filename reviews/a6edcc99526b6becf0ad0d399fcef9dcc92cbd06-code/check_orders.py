"""Recompute the observed orders in the convergence table (tab:conv) of paper/main_light.tex from its own errors and N,
and the 'perturbed' ratios/EOC rows against results/reports/2026-10-29-rerun-078-tables.md where they appear."""
import re, sys, math
tex = open(sys.argv[1]).read()
s = tex[tex.index("Discrete $L^1$ errors and observed orders"):]
s = s[:s.index("\\end{tabular}")]
prev = None; bad = 0; n = 0
for line in s.splitlines():
    if line.startswith("\\multicolumn"): prev = None if "emph" in line else prev; continue
    m = re.match(r"^(\d+) &(.*)\\\\", line)
    if not m: continue
    N = int(m.group(1)); cells = [c.strip() for c in m.group(2).split("&")]
    errs = [float(cells[k]) if cells[k] else None for k in range(0, len(cells), 2)]
    ords = [float(cells[k]) if cells[k] else None for k in range(1, len(cells), 2)]
    if prev:
        N0, e0 = prev
        for a, b, o in zip(e0, errs, ords):
            if a and b and o is not None:
                n += 1; r = math.log(a / b) / math.log(N / N0)
                if abs(r - o) > 0.015: bad += 1; print(f"N={N}: order {o} in table, {r:.3f} from errors")
    prev = (N, errs)
print(f"{n} orders checked, {bad} differ by more than 0.015 (errors are rounded to 3 digits)")

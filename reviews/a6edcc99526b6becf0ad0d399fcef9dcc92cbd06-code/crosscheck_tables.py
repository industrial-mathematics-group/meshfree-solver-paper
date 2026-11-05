"""Cross-check the Euler-shock rows of 2026-10-29-rerun-078-tables.md against the per-run summary lines in
2026-10-29-rerun-078-results.txt (by job id): status, min rho, min p, mass change, steps, runtime."""
import re, sys
R = sys.argv[1]
res = {}
for l in open(f"{R}/2026-10-29-rerun-078-results.txt"):
    p = l.split(None, 1)
    if len(p) == 2 and p[0].isdigit():
        res.setdefault(p[0], []).append(p[1])
tab = open(f"{R}/2026-10-29-rerun-078-tables.md").read().split("## Euler shock problems")[1].split("## Isentropic")[0]
n = bad = 0
for row in tab.splitlines():
    c = [x.strip() for x in row.strip("|").split("|")]
    if len(c) < 13 or not c[12].isdigit():
        continue
    n += 1
    job, grid = c[12], c[1]
    cand = [s for s in res.get(job, []) if f"N={grid}" in s]
    if len(cand) != 1:
        print("no unique line", job, grid, len(cand)); bad += 1; continue
    s = cand[0]
    def g(pat): m = re.search(pat, s); return m.group(1) if m else None
    want = dict(status=c[4], rho=c[7], p=c[8], mass=c[9], steps=c[10], rt=c[11])
    got = dict(status=s.split()[0], rho=g(r"min\(u1\)=(\S+)"), p=g(r"min\(p\)=(\S+)"), mass=g(r"mass drift=(\S+)"),
               steps=g(r"steps=(\d+)"), rt=g(r"runtime=(\S+)"))
    diff = {k: (want[k], got[k]) for k in want if want[k] != got[k]}
    if diff:
        bad += 1; print(job, c[0], c[3], diff)
print(f"{n} rows checked, {bad} mismatches")

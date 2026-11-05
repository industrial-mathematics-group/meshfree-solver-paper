"""LaTeX tables of the stability note from data/*.md and data/*.jsonl (writes tables/*.tex)."""
import json
import os
from collections import defaultdict

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.makedirs(os.path.join(root, "tables"), exist_ok=True)


def sci(x):
    m, e = ("%.1e" % x).split("e")
    return r"%s\cdot10^{%d}" % (m, int(e))


def fmt_re(x):
    return r"$\le 10^{-15}$" if x < 1e-14 else r"$\mathbf{%s}$" % sci(x)


# ---- lattice symbols ------------------------------------------------------------------
rows = defaultdict(dict)
for fn in ("lattice_symbols_1d.md", "lattice_symbols_2d.md"):
    for line in open(os.path.join(root, "data", fn)):
        f = [x.strip() for x in line.strip().strip("|").split("|")]
        if len(f) < 10:
            continue
        D, kappa, a, K, q, orient, re, c2, c3, c54 = f
        rows[(int(D), float(kappa), a, int(K))][orient] = dict(q=int(q), re=float(re), rk3=c3, sr=c54)
sel = [(1, 2.5, "(1)"), (1, 5.5, "(1)"), (2, 2.5, "(1, 0.5)"), (2, 3.5, "(1, 0.5)"), (2, 3.5, "(1, 0)"),
       (2, 5.5, "(1, 0.5)"), (2, 5.5, "(1, 0)")]
with open(os.path.join(root, "tables", "lattice.tex"), "w") as out:
    for D, kappa, a in sel:
        first = True
        for K in range(2, 6):
            r = rows.get((D, kappa, a, K))
            if not r:
                continue
            g, al = r["geometric"], r["aligned"]
            lab = r"%d & %.1f & $%s$" % (D, kappa, a) if first else "&&"
            first = False
            out.write(r"%s & %d & %d & %s & %s & %s & %s & %s & %s\\" % (
                lab, K, g["q"], fmt_re(g["re"]), fmt_re(al["re"]),
                g["rk3"] if g["re"] < 1e-14 else "--", al["rk3"], g["sr"].replace(">", "$>$") if g["re"] < 1e-14 else "--", al["sr"].replace(">", "$>$")) + "\n")
        out.write(r"\midrule" + "\n")

# ---- perturbed-cloud spectra ----------------------------------------------------------
g = defaultdict(list)
for fn in ("spectra_1d.jsonl", "spectra_1d_aligned.jsonl", "spectra_2d.jsonl"):
    p = os.path.join(root, "data", fn)
    if not os.path.exists(p):
        continue
    for line in open(p):
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        o = r.get("orient", "geometric") if r["K"] > 1 else "aligned"
        g[(r["D"], r["kappa"], r["jitter"], r["K"], o)].append(r)
with open(os.path.join(root, "tables", "spectra.tex"), "w") as out:
    last = None
    for key in sorted(g):
        D, kappa, jit, K, o = key
        rs = g[key]
        ns = sorted(set(r["n"] for r in rs))
        al = max(r["alpha"] for r in rs)
        ah = max(r["alpha_h"] for r in rs)
        gr = [r["growth_t1"] for r in rs if "growth_t1" in r]
        if (D, kappa, jit) != last and last is not None:
            out.write(r"\midrule" + "\n")
        lab = r"%d & %.1f & %.1f" % (D, kappa, jit) if (D, kappa, jit) != last else "&&"
        last = (D, kappa, jit)
        tiny = ah < 1e-12                 # round-off threshold on alpha*h (fixed 2026-11-04: was applied to alpha)
        a_s = r"$\le 10^{-12}$" if tiny else "$%s$" % sci(al)
        ah_s = "" if tiny else "$%s$" % sci(ah)
        out.write(r"%s & %d & %s & %s--%s & %s & %s & %s\\" % (
            lab, K, o, ns[0], ns[-1], a_s, ah_s, ("%.2f" % max(gr)) if len(gr) == len(rs) else r"$\infty$") + "\n")
for fn in ("lattice.tex", "spectra.tex"):
    p = os.path.join(root, "tables", fn)
    t = open(p).read().rstrip()
    if t.endswith(r"\midrule"):
        t = t[: -len(r"\midrule")].rstrip()
    open(p, "w").write(t + "\n")
print("tables written")

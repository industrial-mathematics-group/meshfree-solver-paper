"""LaTeX table rows of the high-order stability note from data/ho_*.{jsonl,md} (writes tables/ho_*.tex)."""
import json
import os
import re
from collections import defaultdict

root = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
os.makedirs(os.path.join(root, "tables"), exist_ok=True)


def sci(x):
    if abs(x) < 1e-12:
        return r"$\le10^{-12}$"
    m, e = ("%.1e" % x).split("e")
    return r"$%s\cdot10^{%d}$" % (m, int(e))


def load(fn):
    p = os.path.join(root, "data", fn)
    return [json.loads(l) for l in open(p)] if os.path.exists(p) else []


def rng(vals, fmt="%.3f"):
    lo, hi = min(vals), max(vals)
    return (fmt % lo) if abs(hi - lo) < 1e-12 or (fmt % lo) == (fmt % hi) else (fmt % lo) + "--" + (fmt % hi)


def rng_sci(vals):
    lo, hi = min(vals), max(vals)
    if hi < 1e-12:
        return r"$\le10^{-12}$"
    return sci(hi) if lo <= 1e-12 else (sci(lo) + "--" + sci(hi)).replace("$--$", "--")


# ---- random clouds: numerical abscissa and Kreiss constants ------------------------------------
rows = defaultdict(list)
for r in load("ho_random_1d.jsonl") + load("ho_random_2d.jsonl"):
    rows[(r["D"], r["kappa"], r["jitter"], r["K"], r["orient"])].append(r)
with open(os.path.join(root, "tables", "ho_random.tex"), "w") as out:
    last = None
    for key in sorted(rows):
        D, kappa, jit, K, orient = key
        rs = rows[key]
        ns = sorted(set(r["n"] for r in rs))
        kind = "dual" if D == 1 else "uniform"
        om = [r["omega_h_" + kind] for r in rs]
        kr = [r["kreiss_" + kind] for r in rs if "kreiss_" + kind in r]
        al = [r["alpha_h"] for r in rs]
        head = (D, kappa, jit)
        if last is not None and head != last:
            out.write("\\midrule\n")
        pre = "%d & %g & %g" % head if head != last else "&&"
        last = head
        out.write("%s & %d & %s & %d--%d & %s & %s & %s\\\\\n" % (
            pre, K, orient, ns[0], ns[-1], rng_sci(al), rng(om, "%.4f"), rng(kr) if kr else "$\\infty$"))

# ---- deformed lattices -------------------------------------------------------------------------
rows = defaultdict(list)
for r in load("ho_deformed_1d.jsonl") + load("ho_deformed_2d.jsonl"):
    if r["nmin"] == r["nmax"]:
        rows[(r["D"], r["kappa"], r["A"], r["K"])].append(r)
with open(os.path.join(root, "tables", "ho_deformed.tex"), "w") as out:
    last = None
    for key in sorted(rows):
        D, kappa, A, K = key
        rs = sorted(rows[key], key=lambda r: r["n"])
        head = (D, kappa, A)
        if last is not None and head != last:
            out.write("\\midrule\n")
        pre = "%d & %g & %g" % head if head != last else "&&"
        last = head
        out.write("%s & %d & %s & %s & %s & %s\\\\\n" % (
            pre, K, ", ".join(str(r["n"]) for r in rs), rng_sci([r["alpha_h"] for r in rs]),
            ", ".join("%.1e" % r["omega_V"] for r in rs).replace("e-0", "e-"),
            ", ".join("%.0e" % (r["kreiss_V"] - 1) for r in rs if "kreiss_V" in r).replace("e-0", "e-")))

# ---- Bloch ---------------------------------------------------------------------------------------
rows = defaultdict(list)
for r in load("ho_bloch_1d.jsonl") + load("ho_bloch_2d.jsonl"):
    rows[(r["D"], r["kappa"], r["jitter"], r["K"], r["orient"])].append(r)
with open(os.path.join(root, "tables", "ho_bloch.tex"), "w") as out:
    last = None
    for key in sorted(rows):
        D, kappa, jit, K, orient = key
        rs = rows[key]
        ms = sorted(set(r["m"] for r in rs))
        head = (D, kappa, jit)
        if last is not None and head != last:
            out.write("\\midrule\n")
        pre = "%d & %g & %g" % head if head != last else "&&"
        last = head
        per_m = []
        for m in ms:
            sub = [r for r in rs if r["m"] == m]
            per_m.append("%s / %s" % (sci(max(r["alpha_h"] for r in sub)), "%.3f" % max(r["kreiss"] for r in sub)
                                       if max(r["kreiss"] for r in sub) < 1e3 else "$\\infty$"))
        per_m += [""] * (3 - len(per_m))
        out.write("%s & %d & %s & %s & %s\\\\\n" % (pre, K, orient[:4] + ".", ", ".join(str(m) for m in ms), " & ".join(per_m)))

# ---- pi weight ---------------------------------------------------------------------------------
with open(os.path.join(root, "tables", "ho_pi.tex"), "w") as out:
    last = None
    for fn in ("ho_pi_1d_j02.md", "ho_pi_1d_j02_large.md", "ho_pi_1d_j04.md", "ho_pi_2d_j02.md"):
        p = os.path.join(root, "data", fn)
        if not os.path.exists(p):
            continue
        for line in open(p):
            f = [x.strip() for x in line.strip().strip("|").split("|")]
            if len(f) < 14 or f[0] == "D" or f[0].startswith("-"):
                continue
            D, kappa, jit, n, seed, K, orient, ratio, rho, omV, omp, rms, mx, lb = f
            if seed != "0":
                continue
            head = (D, kappa, jit)
            if last is not None and head != last:
                out.write("\\midrule\n")
            pre = "%s & %s & %s" % head if head != last else "&&"
            last = head
            ratio = ratio.replace(" (not positive)", "")
            out.write("%s & %s & %s & %s & %s & %s & %s & %s & %s & %s\\\\\n" % (
                pre, n, seed, K, orient, ratio, rho if rho != "--" else "--", sci(float(omV)), sci(float(omp)) if omp != "--" else "--", sci(float(lb))))

# ---- local symbols -------------------------------------------------------------------------------
with open(os.path.join(root, "tables", "ho_local.tex"), "w") as out:
    last = None
    for fn in ("ho_local_symbol_k15.md", "ho_local_symbol_j02.md", "ho_local_symbol_j04.md"):
        p = os.path.join(root, "data", fn)
        if not os.path.exists(p):
            continue
        for line in open(p):
            f = [x.strip() for x in line.strip().strip("|").split("|")]
            if len(f) < 12 or f[0] == "kappa" or f[0].startswith("-"):
                continue
            kappa, jit, n, seed, K, nbr, m2, s2, m4, s4, pred, alpha = f
            head = (kappa, jit)
            if last is not None and head != last:
                out.write("\\midrule\n")
            pre = "%s & %s" % head if head != last else "&"
            last = head
            out.write("%s & %s & %s & %s & %s & %s & %s & %s & %s & %s\\\\\n" % (
                pre, n, seed, K, nbr.replace("[", "").replace("]", ""), sci(float(m2)), sci(float(s2)), "%.3f" % float(m4), "%.3f" % float(s4), sci(float(alpha))))

# ---- Lyapunov SDP --------------------------------------------------------------------------------
with open(os.path.join(root, "tables", "ho_lyapunov.tex"), "w") as out:
    for r in load("ho_lyapunov_1d.jsonl"):
        st = r["status"]
        feas = "infeasible" if "infeasible" in st else ("feasible" if r.get("resid", 1) < 1e-3 else "not feasible (residual %.2f)" % r["resid"])
        out.write("%d & %g & %g & %d & %d & %s & %s & %s\\\\\n" % (
            r["D"], r["kappa"], r["jitter"], r["n"], r["K"], r["orient"], feas,
            ("%.2f" % r["rho"]) if "rho" in r and feas == "feasible" else "--"))
print("tables written")

# ---- defects: certificates (1-D) ---------------------------------------------------------------
rows = defaultdict(dict)
for r in load("ho_defect_cert_1d.jsonl"):
    rows[(r["type"], r["K"], r["orient"], r["g"])][r["rho"]] = r
with open(os.path.join(root, "tables", "ho_defect_cert.tex"), "w") as out:
    last = None
    for key in sorted(rows, key=lambda k: (k[0], k[1], k[2], k[3])):
        typ, K, orient, g = key
        rs = rows[key]
        rhos = sorted(rs)
        head = (typ, K, orient)
        if last is not None and head[:2] != last[:2]:
            out.write("\\midrule\n")
        pre = "%s & %d & %s" % (typ, K, orient[:4] + ".") if head != last else "&&"
        last = head
        tcell = ", ".join(("%.0e" % rs[r]["t"]).replace("e-0", "e-") for r in rhos)
        wcell = "%.2f--%.1f" % (min(rs[r]["wmin"] for r in rhos), max(rs[r]["wmax"] for r in rhos))
        ocell = ", ".join(("%.0e" % rs[r]["omegaW_h"]).replace("e-0", "e-") for r in rhos)
        out.write("%s & %g & %s & %s & %s\\\\\n" % (pre, g, tcell, wcell, ocell))

# ---- defects: certificates (2-D) ---------------------------------------------------------------
with open(os.path.join(root, "tables", "ho_defect_cert2d.tex"), "w") as out:
    for r in load("ho_defect_cert_2d.jsonl"):
        out.write("%s & %d & %d & %d & %d & %s & %.2f--%.2f & %s & %.3f\\\\\n" % (
            r["type"], r["K"], r["rho"], r["nz"], r["nzp"], sci(r["t"]), r["wmin"], r["wmax"], sci(r["omegaW_h"]), r["omegaV_h"]))

# ---- defects: Bloch of periodic defect arrays -----------------------------------------------------
rows = defaultdict(dict)
for r in load("ho_defect_bloch_1d.jsonl") + load("ho_defect_bloch_2d.jsonl"):
    rows[(r["D"], r["type"], r["K"], r["orient"])][r["m"]] = r
with open(os.path.join(root, "tables", "ho_defect_bloch.tex"), "w") as out:
    last = None
    for key in sorted(rows, key=lambda k: (k[0], k[1], k[2], k[3])):
        D, typ, K, orient = key
        rs = rows[key]
        ms = sorted(rs)
        head = (D, typ)
        if last is not None and head != last:
            out.write("\\midrule\n")
        pre = "%d & %s" % head if head != last else "&"
        last = head
        acell = ", ".join(("%.1e" % rs[m]["alpha_h"]).replace("e-0", "e-") if rs[m]["alpha_h"] > 1e-12 else "$0$" for m in ms)
        kcell = ", ".join("%.3f" % rs[m]["kreiss"] if rs[m]["kreiss"] < 1e3 else "$\\infty$" for m in ms)
        out.write("%s & %d & %s & %s & %s & %s\\\\\n" % (pre, K, orient[:4] + ".", ", ".join(str(m) for m in ms), acell, kcell))

# ---- defects: superposition ------------------------------------------------------------------------
with open(os.path.join(root, "tables", "ho_defect_super.tex"), "w") as out:
    last = None
    for r in sorted(load("ho_defect_super_1d.jsonl"), key=lambda r: (r["K"], r["A"], r["rho"], r["n"])):
        head = (r["K"], r["A"])
        if last is not None and head != last:
            out.write("\\midrule\n")
        pre = "%d & %g" % head if head != last else "&"
        last = head
        out.write("%s & %d & %d & %d & %s & %s & %s & %s & %s & %.2f--%.1f, %.3f\\\\\n" % (
            pre, r["rho"], r["n"], r["ndef"], "%d/%d/%d" % (r["types"].count("m"), r["types"].count("i"), r["types"].count("s")), sci(r["t_max"]), sci(r["omegaW_h"]), sci(r["omegaV_h"]), sci(abs(r["alpha_h"])),
            r["wmin"], r["wmax"], r["kreiss_V"]))

# ---- defects: random defects -----------------------------------------------------------------------
rows = defaultdict(list)
for r in load("ho_defect_random_1d.jsonl") + load("ho_defect_random_2d.jsonl"):
    rows[(r["D"], r["A"], r["p"], r["K"])].append(r)
with open(os.path.join(root, "tables", "ho_defect_random.tex"), "w") as out:
    last = None
    for key in sorted(rows):
        D, A, p, K = key
        rs = rows[key]
        ns = sorted(set(r["n"] for r in rs))
        head = (D, A, p)
        if last is not None and head != last:
            out.write("\\midrule\n")
        pre = "%d & %g & %g" % head if head != last else "&&"
        last = head
        out.write("%s & %d & %d--%d & %s & %s & %s\\\\\n" % (
            pre, K, ns[0], ns[-1], rng_sci([r["alpha_h"] for r in rs]), rng([r["omega_V_h"] for r in rs], "%.4f"),
            rng([r["kreiss_V"] for r in rs]) if max(r["kreiss_V"] for r in rs) < 1e3 else "%.3f--$\\infty$" % min(r["kreiss_V"] for r in rs)))
print("defect tables written")

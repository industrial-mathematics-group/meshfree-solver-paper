"""Summarise spectra_*.jsonl: per (D, kappa, jitter, orientation, K, n) the maximum over seeds of the spectral
abscissa alpha, of alpha*h, and of ||exp(L)||_2 (t = 1). Usage: python3 summarize_spectra.py file.jsonl ..."""
import json
import sys
from collections import defaultdict

g = defaultdict(list)
for fn in sys.argv[1:]:
    for line in open(fn):
        try:
            r = json.loads(line)
        except json.JSONDecodeError:
            continue
        g[(r["D"], r["kappa"], r["jitter"], r.get("orient", "geometric") if r["K"] > 1 else "aligned", r["K"], r["n"])].append(r)
print("| D | kappa | jitter | orientation | K | n | seeds | max alpha | max alpha*h | max IPR | max norm exp(L) |")
print("|---|---|---|---|---|---|---|---|---|---|---|")
for k in sorted(g):
    rs = g[k]
    al = max(r["alpha"] for r in rs)
    ah = max(r["alpha_h"] for r in rs)
    ipr = max(r["ipr"] for r in rs if r["alpha"] == al)
    gr = [r["growth_t1"] for r in rs if "growth_t1" in r]
    print("| %d | %.1f | %.1f | %s | %d | %d | %d | %.1e | %.1e | %.2f | %s |" % (
        *k, len(rs), al, ah, ipr, ("%.2f" % max(gr)) if len(gr) == len(rs) else "unstable"))

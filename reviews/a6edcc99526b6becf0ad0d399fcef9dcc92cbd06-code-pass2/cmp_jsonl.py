"""Compare regenerated jsonl records with committed ones (match on all non-float fields), report max abs/rel diffs."""
import json, sys, math
old = [json.loads(l) for l in open(sys.argv[1]) if l.strip()]
new = [json.loads(l) for l in open(sys.argv[2]) if l.strip()]
def key(r): return tuple(sorted((k, json.dumps(v)) for k, v in r.items() if (not isinstance(v, (float, list))) or k in ("kappa","jitter","A","p","g","h")))
idx = {}
for r in old: idx.setdefault(key(r), []).append(r)
matched = 0; worst = {}
for r in new:
    k = key(r)
    if k not in idx: continue
    o = idx[k][0]; matched += 1
    for f, v in r.items():
        if isinstance(v, float) and isinstance(o.get(f), float):
            a, b = v, o[f]
            if math.isinf(a) or math.isinf(b) or math.isnan(a) or math.isnan(b):
                d = 0 if a == b else float("inf"); rel = d
            else:
                d = abs(a - b); rel = d / max(abs(b), 1e-300)
            if f not in worst or d > worst[f][0]: worst[f] = (d, rel, b, a)
print(f"{sys.argv[2].split('/')[-1]}: {len(new)} new, {len(old)} old, matched {matched}")
for f, (d, rel, b, a) in sorted(worst.items()):
    print(f"   {f:14s} max|diff|={d:.2e} (old {b:.6g} new {a:.6g})")

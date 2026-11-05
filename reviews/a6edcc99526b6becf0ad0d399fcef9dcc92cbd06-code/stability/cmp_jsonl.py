"""Compare regenerated jsonl with committed: match records on non-float keys, report max relative diff per numeric field."""
import json, sys, math
from collections import defaultdict
orig, new = sys.argv[1], sys.argv[2]
keys = sys.argv[3].split(",")
absfloor = float(sys.argv[4]) if len(sys.argv) > 4 else 1e-12
def load(f): return [json.loads(l) for l in open(f) if l.strip()]
O = {tuple(r.get(k, "geometric" if k == "orient" else None) for k in keys): r for r in load(orig)}
N = {tuple(r.get(k, "geometric" if k == "orient" else None) for k in keys): r for r in load(new)}
common = set(O) & set(N)
print(f"{orig.split('/')[-1]}: orig {len(O)}, new {len(N)}, matched {len(common)}")
worst = defaultdict(lambda: (0.0, None))
for k in common:
    for f, v in O[k].items():
        w = N[k].get(f)
        if isinstance(v, float) and isinstance(w, (float, int)):
            if math.isinf(v) and math.isinf(w): continue
            d = abs(v - w) / max(abs(v), abs(w), absfloor)
            if d > worst[f][0]: worst[f] = (d, (k, v, w))
        elif f not in ("theta_worst", "theta_kreiss") and v != w and not isinstance(v, float):
            print("  MISMATCH", k, f, v, w)
for f, (d, ex) in sorted(worst.items()):
    print(f"  {f}: max rel diff {d:.1e}" + (f"  e.g. {ex}" if d > 1e-6 else ""))

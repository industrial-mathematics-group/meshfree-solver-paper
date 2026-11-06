"""Compare a fresh run of stability/scripts/ho_defect_bloch.py with the committed 1-D jsonl files.

Regenerate first (from the repository root, about 10 s):
  python3 stability/scripts/ho_defect_bloch.py 1 8,16,32 2,3,4 64 NEW.jsonl geometric,aligned merge,insert,shift
Then: python3 compare_defect_bloch.py NEW.jsonl
Also prints the K = 4 aligned insert records, which are not zero to round-off (finding N1)."""
import json, sys, os
root = os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..")
new = [json.loads(l) for l in open(sys.argv[1])]
old = {}
for f in ["ho_defect_bloch_1d.jsonl", "ho_defect_bloch_1d_insert_shift.jsonl"]:
    for l in open(os.path.join(root, "stability", "data", f)):
        r = json.loads(l); old.setdefault((r["type"], r["m"], r["K"], r["orient"]), []).append(r)
bad = 0
for r in new:
    for o in old.get((r["type"], r["m"], r["K"], r["orient"]), []):
        if abs(o["alpha_h"] - r["alpha_h"]) > 1e-12 + 1e-6 * abs(r["alpha_h"]) or abs(o["kreiss"] - r["kreiss"]) > 1e-6:
            bad += 1; print("DIFF", r["type"], r["m"], r["K"], r["orient"], o["alpha_h"], r["alpha_h"])
print("records compared:", len(new), "differences:", bad)
for k, rs in sorted(old.items()):
    if k[0] == "insert" and k[2] == 4 and k[3] == "aligned":
        print("insert K=4 aligned m=%d: alpha_h = %.3e, Kreiss %.4f" % (k[1], rs[0]["alpha_h"], rs[0]["kreiss"]))

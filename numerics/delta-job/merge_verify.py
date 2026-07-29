"""Merge shards into delta_table.jsonl and verify: contiguity 0..MMAX,
duplicate consistency, radius audit, monotonicity, the proven bound
|delta_m| <= log2*m*log(m+1)+1, and spot-recomputation of 5 random new rows."""
import sys, json, glob, math, random, re
from delta_arb import delta_arb

def num(s):
    m = re.match(r"\[?(-?[0-9.]+(?:e[+-]?[0-9]+)?)", s); return float(m.group(1))

def main(mmax):
    rows = {}
    for line in open("delta_table.jsonl"):
        r = json.loads(line); rows[r["m"]] = r
    for f in sorted(glob.glob("shards/shard_*.jsonl")):
        for line in open(f):
            r = json.loads(line)
            if r["m"] in rows:
                assert rows[r["m"]]["mid"] == r["mid"], f"MISMATCH at m={r['m']}"
            rows[r["m"]] = r
    ms = sorted(rows)
    assert ms == list(range(mmax + 1)), f"GAP: have {len(ms)} rows, missing " + str(
        sorted(set(range(mmax + 1)) - set(ms))[:10])
    with open("delta_table.jsonl", "w") as fh:
        for m in ms:
            fh.write(json.dumps(rows[m]) + "\n")
    print(f"merged: m=0..{mmax}, {len(ms)} rows")
    worst_rad = max(num(rows[m]["rad"]) for m in ms)
    print(f"worst radius: {worst_rad:.2e}  (require < 1e-60)"); assert worst_rad < 1e-60
    mids = {m: num(rows[m]["mid"]) for m in ms}
    dips = [m for m in range(10, mmax) if mids[m + 1] < mids[m]]
    assert not dips, f"non-monotone at {dips[:5]}"
    bad = [m for m in ms if abs(mids[m]) > math.log(2) * m * math.log(m + 1) + 1 + 1e-9]
    assert not bad, f"proven bound violated at {bad[:5]}"
    print("monotone: OK; proven |delta| bound: OK over all rows")
    random.seed(7)
    for m in random.sample(range(1046, mmax + 1), 5):
        d = delta_arb(m, int(2.2 * m) + 300)
        assert abs(float(d.mid()) - mids[m]) <= float(d.rad()) + 1e-20, f"recompute mismatch m={m}"
        print(f"spot-recompute m={m}: OK")
    print("MERGE+VERIFY PASSED")

if __name__ == "__main__":
    main(int(sys.argv[1]) if len(sys.argv) > 1 else 2440)

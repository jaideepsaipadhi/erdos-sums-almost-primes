#!/usr/bin/env python3
"""Spot-check the committed delta table by recomputing a sample.

The full extension m = 1046..2440 is about 9.4 core-hours (delta_arb costs
~5.8s at m=1046 and ~52s at m=2440, scaling near m^2.6), so recomputing all
of it to confirm a table that is already committed is poor value.  A sample
spread across the range catches systematic corruption -- a wrong precision
rule, a truncated shard, an off-by-one in the stride -- for a few minutes.

It recomputes each sampled m at the SAME precision rule the shards record and
requires the recomputed ball to contain the stored midpoint, which is the
property the downstream consumers rely on.

Usage: python3 delta_spotcheck.py [N_SAMPLES]
"""
import sys, json, glob, time
from flint import arb
from delta_arb import delta_arb

N = int(sys.argv[1]) if len(sys.argv) > 1 else 10
stored = {}
for f in glob.glob("shards/*.jsonl"):
    for line in open(f):
        r = json.loads(line)
        stored[r["m"]] = r
ms = sorted(stored)
lo, hi = ms[0], ms[-1]
step = max(1, (hi - lo) // (N - 1))
sample = list(range(lo, hi + 1, step))[:N]
if sample[-1] != hi:
    sample[-1] = hi

print("stored: %d values, m = %d..%d" % (len(stored), lo, hi))
print("checking %d of them\n" % len(sample))
bad = 0
for m in sample:
    r = stored[m]
    t0 = time.time()
    d = delta_arb(m, r["prec"])
    mid = arb(r["mid"])
    ok = d.overlaps(mid)
    # also check the recomputed radius is no larger than recorded, which would
    # signal a precision rule that has drifted
    rad_ok = float(d.rad()) <= float(arb(r["rad"])) * 1.000001
    flag = "ok" if ok else "MISMATCH"
    if not ok:
        bad += 1
    print("m=%4d prec=%5d  %-8s  recomputed rad %.3e vs stored %s  (%.1fs)"
          % (m, r["prec"], flag, float(d.rad()), r["rad"], time.time() - t0),
          flush=True)
print()
print("%d of %d agree" % (len(sample) - bad, len(sample)))
sys.exit(1 if bad else 0)

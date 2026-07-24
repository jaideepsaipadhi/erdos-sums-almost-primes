#!/usr/bin/env python3
import sys, io
PATH = sys.argv[1] if len(sys.argv) > 1 else "Banksmartin/Basic.lean"
OLD = """((x / k) / Real.log (x / k)) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)"""
NEW = """((x / k) / Real.log (x / k)) := by
    conv_rhs => rw [Finset.sum_filter]
    refine Finset.sum_congr rfl (fun k _ => ?_)"""
with io.open(PATH, "r", encoding="utf-8") as fh:
    s = fh.read()
n = s.count(OLD)
if n != 1:
    print("ERROR: expected exactly 1 match, found", n, "- aborting."); sys.exit(1)
s = s.replace(OLD, NEW)
with io.open(PATH, "w", encoding="utf-8") as fh:
    fh.write(s)
print("OK: rw constrained to conv_rhs.")

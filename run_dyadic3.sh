#!/usr/bin/env bash
set -u

echo "===== STEP 1: applying conv_rhs fix ====="
cat > fix1.py << 'PYEOF'
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
PYEOF
python3 fix1.py

echo "===== STEP 2: lake build ====="
lake build

echo "===== STEP 3 (PLEASE INCLUDE IN PASTE): primeCounting_le_bound_own ====="
sed -n '/^theorem primeCounting_le_bound_own/,/^theorem piK_bound_one/p' Banksmartin/Basic.lean

echo "===== STEP 4 (PLEASE INCLUDE IN PASTE): integral_term_bound_gen body ====="
sed -n '/^theorem integral_term_bound_gen/,/^theorem integral_term_bound (/p' Banksmartin/Basic.lean

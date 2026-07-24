#!/usr/bin/env bash
set -u

echo "===== STEP 1: writing fix5.py ====="
cat > fix5.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io
PATH = sys.argv[1] if len(sys.argv) > 1 else "Banksmartin/Basic.lean"
R = "\u211d"
with io.open(PATH, "r", encoding="utf-8") as fh:
    lines = fh.read().split("\n")
joined = "\n".join(lines)
n1 = joined.count("(Real.log_pow J 2).symm")
if n1 != 1:
    print("ERROR: log_pow fix - expected 1 match, found", n1); sys.exit(1)
joined = joined.replace("(Real.log_pow J 2).symm", "by rw [Real.log_pow]")
lines = joined.split("\n")
expected = "    have hden_lower : (0:" + R + ") <"
hits = [i for i, l in enumerate(lines) if l.rstrip() == expected]
if len(hits) != 1:
    print("ERROR: hden_lower fix - expected 1 matching line, found", len(hits)); sys.exit(1)
i = hits[0]
lines[i] = "    have hden_lower :"
lines[i + 1] = "        (0:" + R + ") < " + lines[i + 1].lstrip()
print("OK: both fixes applied")
stragglers = [k + 1 for k, l in enumerate(lines) if l.rstrip().endswith("<") and l.strip() != "<"]
if stragglers:
    print("WARNING: other lines still ending in '<':", stragglers)
else:
    print("no other trailing-< lines")
with io.open(PATH, "w", encoding="utf-8") as fh:
    fh.write("\n".join(lines))
PYEOF

echo "===== STEP 2: applying fixes ====="
python3 fix5.py

echo "===== STEP 3: lake build ====="
lake build

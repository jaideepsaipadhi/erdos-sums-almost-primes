#!/usr/bin/env bash
set -u

echo "===== STEP 1: raw bytes of the hden_lower region (ground truth) ====="
grep -n -A2 "hden_lower :" Banksmartin/Basic.lean | cat -A | head -12

echo "===== STEP 2: writing fix5b.py ====="
cat > fix5b.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io
PATH = sys.argv[1] if len(sys.argv) > 1 else "Banksmartin/Basic.lean"
with io.open(PATH, "r", encoding="utf-8", newline="") as fh:
    raw = fh.read()
crlf = "\r" in raw
s = raw.replace("\r\n", "\n").replace("\r", "\n")
lines = s.split("\n")

n1 = s.count("(Real.log_pow J 2).symm")
if n1 == 1:
    s = s.replace("(Real.log_pow J 2).symm", "by rw [Real.log_pow]")
    lines = s.split("\n")
    print("OK: log_pow fix")
elif "by rw [Real.log_pow]" in s and n1 == 0:
    print("SKIP: log_pow fix already applied")
else:
    print("ERROR: log_pow fix - found", n1, "matches"); sys.exit(1)

hits = [k for k, l in enumerate(lines) if "have hden_lower" in l]
if len(hits) != 1:
    print("ERROR: expected 1 hden_lower line, found", len(hits))
    for k in hits:
        print("  line", k + 1, repr(lines[k]))
    sys.exit(1)
i = hits[0]
cur = lines[i]
if cur.rstrip().endswith("<"):
    marker = "have hden_lower :"
    p = cur.find(marker)
    if p < 0:
        print("ERROR: marker not found in line", i + 1, repr(cur)); sys.exit(1)
    indent = cur[:p]
    tail = cur[p + len(marker):].strip()
    lines[i] = indent + marker
    lines[i + 1] = indent + "    " + tail + " " + lines[i + 1].lstrip()
    print("OK: hden_lower merged. New lines:")
    print("  ", repr(lines[i]))
    print("  ", repr(lines[i + 1]))
elif ":= by" in cur or cur.strip() == "have hden_lower :":
    print("SKIP: hden_lower already fixed:", repr(cur))
else:
    print("ERROR: hden_lower line in unexpected shape:")
    print("  line", i + 1, repr(cur))
    print("  line", i + 2, repr(lines[i + 1]))
    sys.exit(1)
if crlf:
    print("NOTE: CR characters found and normalized to LF")
with io.open(PATH, "w", encoding="utf-8", newline="") as fh:
    fh.write("\n".join(lines))
print("file written")
PYEOF

echo "===== STEP 3: applying fixes ====="
if python3 fix5b.py; then
  echo "===== STEP 4: lake build ====="
  lake build
else
  echo "FIX FAILED - skipping build. Paste this whole output."
fi

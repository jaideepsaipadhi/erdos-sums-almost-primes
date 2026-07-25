#!/usr/bin/env bash
set -u

cat > patch_fk_a.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io, base64, gzip, hashlib

PATH = "Banksmartin/Basic.lean"
MD5 = "ebd6b06c6436e6829b6ca7d723bdbfe9"
B = """
H4sIALfuY2oC/70Yy27bRvCur5hbSFuWLfWmVLkUKFAUUoogt8AmKHJp0SaXCknZUdFDUKSFc2sP
PQbpoUDbL+i9n6Iv6czsLsmlKEvOozqI5O683727J yfwXCSiCLJlLC9hnq1kOIaln5exn0CxSgvI
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
"""

s = gzip.decompress(base64.b64decode("".join(B.split()))).decode("utf-8")
if hashlib.md5(s.encode()).hexdigest() != MD5:
    print("ERROR: payload md5 mismatch - aborting."); sys.exit(1)
with io.open(PATH, "r", encoding="utf-8") as fh:
    f = fh.read()
if "theorem telescope_sqrt" in f:
    print("ERROR: patch already applied; aborting."); sys.exit(1)
i = f.find("/-- DEEP FACT")
if i < 0:
    print("ERROR: DEEP FACT anchor not found; aborting."); sys.exit(1)
f = f[:i] + s.rstrip("\n") + "\n\n" + f[i:]
with io.open(PATH, "w", encoding="utf-8") as fh:
    fh.write(f)
print("OK: four fk_summable support lemmas inserted.")
PYEOF

if python3 patch_fk_a.py; then
  echo "===== lake build ====="
  lake build
else
  echo "PATCH FAILED - skipping build. Paste this whole output."
fi

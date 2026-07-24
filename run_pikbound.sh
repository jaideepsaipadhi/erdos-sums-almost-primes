#!/usr/bin/env bash
set -u

cat > patch_pikbound.py << 'PYEOF'
#!/usr/bin/env python3
import sys, io

PATH = "Banksmartin/Basic.lean"
with io.open(PATH, "r", encoding="utf-8") as fh:
    s = fh.read()

if "exact hbound 2 x hx" in s:
    print("ERROR: patch already applied; aborting."); sys.exit(1)

# locate the early block: DEEP FACT docstring .. end of fk_summable's sorry line
i = s.find("/-- DEEP FACT")
if i < 0:
    print("ERROR: DEEP FACT docstring not found"); sys.exit(1)
endmark = "sorry -- partial summation against hbound; standard but not short."
j = s.find(endmark, i)
if j < 0:
    print("ERROR: fk_summable sorry line not found"); sys.exit(1)
j = s.find("\n", j) + 1
block = s[i:j]

# locate insertion point: before the final theorem, docstring-aware
e = s.find("theorem erdos_sums_increase_from_six")
if e < 0:
    print("ERROR: final theorem not found"); sys.exit(1)
head = s[:e]
ds = head.rfind("/--")
if ds >= 0 and "-/" in head[ds:] and head[head.find("-/", ds) + 2:].strip() == "":
    e = ds

# dependency guard: nothing between old and new position may use these names
between = s[j:e]
for name in ("piK_bound", "fk_summable"):
    if name in between:
        k = j + between.find(name)
        line = s[:k].count("\n") + 1
        print("ERROR: dependency guard -", name, "referenced at line", line,
              "between old and new position; move unsafe, aborting.")
        sys.exit(1)

# rewrite the block: swap piK_bound's sorry-comment for the corollary proof
ps = block.find("  sorry -- THE deep step")
if ps < 0:
    print("ERROR: piK_bound sorry anchor not found in block"); sys.exit(1)
pe_anchor = "classical elementary argument)."
pe = block.find(pe_anchor, ps)
if pe < 0:
    print("ERROR: piK_bound sorry end anchor not found"); sys.exit(1)
pe = block.find("\n", pe) + 1
proof = ("  obtain \u27e8C, hC, hbound\u27e9 := piKFrom_bound k hk\n"
         "  refine \u27e8C, hC, fun x hx => ?_\u27e9\n"
         "  rw [piK_eq_piKFrom_two]\n"
         "  exact hbound 2 x hx\n")
newblock = block[:ps] + proof + block[pe:]
newblock = newblock.replace("not yet formalized", "now formalized via piKFrom_bound")

# splice: remove old block, insert new block before the final theorem
s2 = s[:i] + s[j:]
shift = j - i
e2 = e - shift
s2 = s2[:e2] + newblock + "\n" + s2[e2:]
with io.open(PATH, "w", encoding="utf-8") as fh:
    fh.write(s2)
print("OK: block moved below piKFrom_bound; piK_bound proven as corollary.")
print("    fk_summable retains its sorry (next real target).")
PYEOF

if python3 patch_pikbound.py; then
  echo "===== lake build ====="
  lake build
else
  echo "PATCH FAILED - skipping build. Paste this whole output."
fi

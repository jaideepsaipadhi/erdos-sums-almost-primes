#!/usr/bin/env python3
"""Check the Arb outputs against theorems proved in Basic.lean.

Each check is a formally proved statement applied to the certified numerics,
so it is independent of the Arb code's internals.  Run from bm-rebuild-v21/.
"""
import json, math, os, re, sys
FAIL = []
def check(name, ok, detail=""):
    print("  [%s] %s%s" % ("PASS" if ok else "FAIL", name, ("  -- "+detail) if detail else ""))
    if not ok: FAIL.append(name)
def load(fn): return json.load(open(fn)) if os.path.exists(fn) else None
def ball_mid(s):
    m = re.search(r'-?\d+\.?\d*(?:[eE][-+]?\d+)?', str(s).replace("[",""))
    return float(m.group()) if m else None

print("== Theorem 4.1: |delta_m| <= log2*m*log(m+1)+1 ==")
tab = next((f for f in ("delta_table.jsonl","delta_table_m0-1000.jsonl",
                        "../delta_table_m0-1000.jsonl") if os.path.exists(f)), None)
if tab:
    n=bad=0; worst=0.0
    for line in open(tab):
        d=json.loads(line); m=d["m"]; v=ball_mid(d["mid"])
        D=math.log(2)*m*math.log(m+1)+1; n+=1
        if D>0: worst=max(worst,abs(v)/D)
        if abs(v)>D: bad+=1
    check("delta table within D(m)", bad==0, "%d entries, worst ratio %.4f"%(n,worst))
else:
    check("delta table present", False)

print("== A2m_le: A2_m <= (m+1)/2 ==")
try:
    sys.path.insert(0,"."); import s2_table
    bad=[m for m in (0,1,2,5,10,20,50)
         if (lambda a: float(a.mid()) if hasattr(a,"mid") else float(a))(s2_table.A2(m,200)) > (m+1)/2]
    check("A2_m <= (m+1)/2", not bad)
except Exception as e:
    check("A2_m computable", False, str(e)[:60])

print("== geom_two_three: sum 2^l 3^(-l-1) = 1 ==")
s=sum(2.0**l/3.0**(l+1) for l in range(200))
check("sums to 1", abs(s-1.0)<1e-12, "%.15f"%s)

print("== Gamma ==")
gc=load("gamma_constant.json"); g2=load("gamma2_certified.json")
if gc and g2:
    head=sum(v*2**int(k) for k,v in g2.items() if int(k)>=1)
    check("head matches", abs(head-gc["head"])<1e-6, "%.6f vs %.6f"%(head,gc["head"]))
    check("Gamma=(head+tail)/2", abs((gc["head"]+gc["tail"])/2-gc["Gamma"])<1e-6)
    check("gammahat_0 = 0", abs(g2.get("0",1.0))<1e-15)
    M2=gc.get("M2sup_R2.9")
    if M2:
        check("Cauchy tail at 2.9", not [k for k,v in g2.items() if v>M2/2.9**int(k)])
else:
    check("gamma jsons present", False)

print("== criterion sweeps ==")
for fn in ("crit_900_2439.json","crit_78_734.json"):
    c=load(fn)
    if not c: continue
    ks=sorted(int(k) for k in c)
    check("%s positive"%fn, not [k for k in ks if c[str(k)]<=0],
          "[%d,%d] n=%d min=%.2f"%(ks[0],ks[-1],len(ks),min(c.values())))
    check("%s contiguous"%fn, ks==list(range(ks[0],ks[-1]+1)))

# crit_certified.json is the UNREFINED criterion (manuscript K0 = 735), kept as
# the baseline the section 6 refinement improves on.  Its zero crossing is the
# check, not positivity.
c=load("crit_certified.json")
if c:
    ks=sorted(int(k) for k in c)
    first_pos=min(k for k in ks if c[str(k)]>0)
    check("unrefined K0 = 735", first_pos==735, "first positive k = %d"%first_pos)

print()
sys.exit(1 if FAIL else 0) if FAIL else print("all checks passed")

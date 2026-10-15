"""Merge certified chunks -> certificate.json (+ human-readable verdicts).
Usage: python3 certificate.py KMAX PREC
Reads cchunks/, verifies panel coverage, adds tail balls, emits certificate
with outward-rounded decimal enclosures, per-pair monotonicity gaps, params,
versions, and a SHA-256 of the payload."""
from flint import arb, ctx
import glob, sys, json, hashlib, subprocess, datetime

KMAX, PREC = int(sys.argv[1]), int(sys.argv[2])
sys.argv = ['x', str(KMAX), str(PREC)]
import certified as C
ctx.prec = PREC
D = int(PREC*0.30103) - 5          # decimal digits to store

def outward(x):
    """Decimal [lo,hi] strings rigorously containing arb ball x."""
    pad = arb(10)**(-D+2)
    lo = (x - arb(0).union(pad.union(-pad))).lower()
    hi = (x + arb(0).union(pad.union(-pad))).upper()
    return arb(lo).str(D, radius=False), arb(hi).str(D, radius=False)

fk=[arb(0)]*(KMAX+1); fks=[arb(0)]*(KMAX+1)
files = sorted(glob.glob("cchunks/c*.txt"))
spans = [tuple(map(int, f.split('/c')[1].split('.')[0].split('_'))) for f in files]
cov = 0
for a,b in spans:
    assert a == cov, f"gap before panel {a}"
    cov = b
assert cov == C.NPANEL, f"coverage {cov} != {C.NPANEL}"
def parse_val(mid_s, rad_s):
    x = arb(mid_s)
    pad = abs(x)*arb(10)**(-166) + arb(10)**(-2000)   # decimal round-trip slack
    r = arb(rad_s) + pad
    return x + arb(0).union(r.union(-r))

for f in files:
    L = open(f).read().splitlines()
    assert len(L) == KMAX + 2, f"{f}: truncated ({len(L)} lines, need {KMAX+2})"
    assert L[0].startswith("#PARAMS") and f"KMAX={KMAX} " in L[0]+" " and f"PREC={PREC} " in L[0]+" ",         f"{f}: parameter mismatch: {L[0]}"
    assert L[-1] == "#END", f"{f}: missing end marker (interrupted write)"
    for line in L[1:-1]:
        p = line.split(); k = int(p[0])
        fk[k]  += parse_val(p[1], p[2])
        fks[k] += parse_val(p[3], p[4])
for k in range(2, KMAX+1):
    t = C.tail_large_s(k) + C.tail_near_1(k)
    fk[k] += t; fks[k] += t

entries, pairs, pairs_sf = [], [], []
for k in range(2, KMAX+1):
    lo, hi = outward(fk[k]); slo, shi = outward(fks[k])
    entries.append({"k": k, "f_k": [lo, hi], "f_k_squarefree": [slo, shi],
                    "radius": arb(fk[k].rad()).str(8, radius=False),
                    "radius_sf": arb(fks[k].rad()).str(8, radius=False)})
for k in range(6, KMAX):
    g = (fk[k+1] - fk[k]).lower()
    pairs.append({"k": k, "claim": f"f_{k} < f_{k+1}",
                  "certified_gap_lower_bound": arb(g).str(10, radius=False),
                  "verified": bool(arb(g) > 0)})
for k in range(2, KMAX):
    g = (fks[k] - fks[k+1]).lower()
    pairs_sf.append({"k": k, "claim": f"f*_{k} > f*_{k+1}",
                     "certified_gap_lower_bound": arb(g).str(10, radius=False),
                     "verified": bool(arb(g) > 0)})

def ver(cmd):
    try: return subprocess.check_output(cmd, shell=True, text=True).strip()
    except Exception: return "unavailable"

payload = {
  "title": "Certified enclosures of f(N_k) and f(N_k*), Erdos sums of k-almost primes",
  "definition": "f(N_k) = sum over n with Omega(n)=k of 1/(n log n) = int_1^inf P_k(s) ds",
  "method": "Ball arithmetic (Arb/FLINT). Error sources bounded: (A) arithmetic, "
            "(B) Mobius-series truncation for P(s), (C) Gauss-Legendre discretization "
            "via per-panel Bernstein-ellipse bounds, (D) interval-Newton certified "
            "nodes/weights, (E) tail s>=S0 via P(s)<=2.78*2^-s (s>=2), "
            "(F) tail s->1+ via P_k(s)<=log(1/(s-1))^k/k! and incomplete-Gamma bound.",
  "parameters": {"KMAX": KMAX, "PREC_bits": PREC, "ULO": C.ULO, "UHI": C.UHI,
                 "panel_width": C.H, "gl_points": C.NGL, "ellipse_delta": C.DELTA,
                 "npanel": C.NPANEL, "quadrature_bound":
                 "Trefethen ATAP Thm 19.3 form with 10x safety factor"},
  "trusted_base": "FLINT/Arb ball arithmetic; python-flint bindings",
  "versions": {"python_flint": ver("python3 -c 'import flint;print(flint.__version__)'"),
               "python": sys.version.split()[0],
               "date_utc": datetime.datetime.now(datetime.timezone.utc).isoformat()},
  "enclosures": entries,
  "monotonicity_f_k_increasing": pairs,
  "monotonicity_squarefree_decreasing": pairs_sf,
  "caveats": ["Quadrature constant 64/15 with denominator (1-rho^-2) is the Gauss "
              "bound of Trefethen, SIAM Rev. 50 (2008) 67-87, Thm 4.5 eq. (4.14) "
              "(= ATAP Thm 19.3), applied at rho^-2N with N the node count and an "
              "additional 10x factor.  Verified against the source 2026-10-14.",
              "Enclosure bounds [lo,hi] are outward-rounded decimals; binary balls are tighter."]
}
blob = json.dumps(payload, indent=1, sort_keys=True)
payload["sha256_of_payload_without_hash"] = hashlib.sha256(blob.encode()).hexdigest()
open("certificate.json","w").write(json.dumps(payload, indent=1, sort_keys=True))
allv = all(p["verified"] for p in pairs) and all(p["verified"] for p in pairs_sf)
print(f"certificate.json written; all {len(pairs)+len(pairs_sf)} claims verified: {allv}")
if not allv:
    print("\nFAILURE DIAGNOSTICS:")
    for nm, ps in (("f_k increasing", pairs), ("f*_k decreasing", pairs_sf)):
        bad = [p for p in ps if not p["verified"]]
        if bad:
            print(f"  {nm}: {len(bad)} failures at k =", [p["k"] for p in bad][:20])
            for p in bad[:5]:
                print(f"    k={p['k']}: gap_lb={p['certified_gap_lower_bound']}")
    for e in entries:
        if e["k"] % 25 == 0 or e["k"] == KMAX:
            print(f"  k={e['k']}: radius={e['radius']} radius_sf={e['radius_sf']}")
    sys.exit(1)

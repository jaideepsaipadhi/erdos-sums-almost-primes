"""Cross-validation of the assembly identity against the independent f_k pipeline.

For k in [100, 200]:
    E_fk(k)   := 2^k (1 - f_k) - a1 k^2          (f_k enclosure from certificate.json)
    E_asm(k)  := E_parts(k) +/- E1bound(k)        (assembly side, this rebuild)
The true E(k) lies in BOTH intervals, so they MUST overlap for every k.
A single non-overlap = a glue error in the assembly derivation (sign / factor /
dropped term) — exactly the class of bug no per-component check can catch.

Run from inside the bm-rebuild-v2 directory (needs delta_table.jsonl covering
m <= 200 [it covers 0..1000], ci_certified.py, ci_certified.json,
tail_constants.json, beta_certified.json, m1_constant.json, delta_conv.py)
with certificate.json accessible:

    python3 crossval_certificate.py /path/to/certificate.json

ADAPT load_fk() below to your certificate.json schema. It must return, for each
k in [100, 200], a certified enclosure of f_k as (lo, hi) decimal strings (or
floats at >= 60 significant digits — your certificate stores round-trip padded
decimals, use those verbatim).
"""
import sys, json, re
from flint import arb, ctx

def parse_ball(s):
    m = re.match(r"\[?(-?[0-9.]+(?:e[+-]?[0-9]+)?)(?: \+/- ([0-9.e+-]+))?\]?", s)
    a = arb(m.group(1)); r = arb(m.group(2) or "0")
    return a.union(a - r).union(a + r)

def load_artifacts(prec):
    ctx.prec = prec
    ci = {int(k): parse_ball(v) for k, v in json.load(open("ci_certified.json")).items()}
    tc = json.load(open("tail_constants.json"))
    rho = parse_ball(tc["rho"])
    supH = arb(tc["supH_R4.2_upper"])
    delta = {}
    for line in open("delta_table.jsonl"):
        r = json.loads(line)
        mid = parse_ball(r["mid"]); rad = arb(r["rad"].strip("[]").split(" ")[0])
        delta[r["m"]] = mid.union(mid - rad).union(mid + rad)
    beta = {int(k): arb(str(v)) for k, v in json.load(open("beta_certified.json")).items()}
    M1 = arb(str(json.load(open("m1_constant.json"))["M1_R2.9"]))
    return ci, rho, supH, delta, beta, M1

def load_fk(path):
    """ADAPT THIS to your certificate.json schema.
    Expected return: dict k -> (lo_str, hi_str) certified enclosure of f_k.
    Below is a guess at the schema; edit freely."""
    c = json.load(open(path))
    out = {}
    # --- common possibilities; keep whichever matches, delete the rest ---
    if "enclosures" in c:                      # e.g. {"enclosures": {"f_100": {"lo": "...", "hi": "..."}}}
        for key, v in c["enclosures"].items():
            m = re.match(r"f_?(\d+)$", key)
            if m:
                out[int(m.group(1))] = (v["lo"], v["hi"])
    elif "f" in c:                             # e.g. {"f": {"100": ["lo","hi"], ...}}
        for k, v in c["f"].items():
            out[int(k)] = (v[0], v[1])
    if not out:
        raise RuntimeError("adapt load_fk() to your certificate schema; top-level keys: " + str(list(c.keys())[:10]))
    return out

def main(cert_path, klo=100, khi=200, prec=800):
    ctx.prec = prec
    ci, rho, supH, delta, beta, M1 = load_artifacts(prec)
    from ci_certified import certified_d
    ln2 = arb(2).log(); q = ln2 / 4
    d = certified_d(2000000, prec)
    a1 = d * q

    def coeff_ball(i):
        if i <= 30:
            return ci[i]
        c = -rho / arb(3) ** (i + 1); h = supH / arb("4.2") ** i
        return c.union(c - h).union(c + h)

    Uc, Vc = {}, {}
    U = arb(0); V = arb(0)
    for i in range(0, khi + 1):
        t = arb(2) ** i * coeff_ball(i)
        U += i * t; V += i * i * t
        Uc[i] = U; Vc[i] = V

    def Delta(k):
        s = arb(0)
        for i in range(0, min(30, k) + 1):
            s += arb(2) ** i * ci[i] * delta[k - i]
        for i in range(31, k + 1):
            s += arb(2) ** i * coeff_ball(i) * delta[k - i]
        return s

    def tails(k):
        r3 = arb(1) / 3
        w_main = -rho * (arb(3) ** (-(k + 2))) / (1 - r3)
        w_err = supH * (arb("4.2") ** (-(k + 1))) / (1 - 1 / arb("4.2"))
        w = w_main.union(w_main - w_err).union(w_main + w_err)
        r23 = arb(2) / 3
        W_main = -rho / 3 * (r23 ** (k + 1)) / (1 - r23)
        rW = arb(2) / arb("4.2")
        W_err = supH * (rW ** (k + 1)) / (1 - rW)
        W = W_main.union(W_main - W_err).union(W_main + W_err)
        return w, W

    def Eexp(k):
        w, W = tails(k)
        hi = 1 / (k * ln2 * (1 - arb(2) ** (-k)))
        T = (hi / 2).union(arb(0)).union(hi)
        return arb(2) ** (k + 1) * w - q * arb(k) ** 2 * W - T

    def E1bound(k):
        s = arb(0)
        for i in range(1, min(30, k) + 1):
            s += beta[i] * arb(2) ** i * (k + 1 - i)
        r = arb(2) / arb("2.9"); tail = arb(0)
        if k >= 31:
            ri = r ** 31
            for i in range(31, k + 1):
                tail += ri * (k + 1 - i); ri *= r
        return (s + M1 * tail) / 2

    fk = load_fk(cert_path)
    bad, worst = [], None
    for k in range(klo, khi + 1):
        if k not in fk:
            continue
        lo, hi = fk[k]
        f = arb(lo).union(arb(hi))
        E_fk = arb(2) ** k * (1 - f) - a1 * arb(k) ** 2
        core = -q * (2 * k * Uc[k] - Vc[k]) - Delta(k) + Eexp(k)
        b = E1bound(k)
        E_lo = core - b; E_hi = core + b
        # overlap test: E_fk interval must intersect [E_lo.lower(), E_hi.upper()]
        overlap = not (float(E_fk.upper()) < float(E_lo.lower()) or float(E_fk.lower()) > float(E_hi.upper()))
        # centering diagnostic: implied E1(k) = core_mid - E_fk_mid, vs allowance b
        implied = float((core - E_fk).mid()); allow = float(b.mid())
        frac = abs(implied) / allow if allow else 0
        if not overlap:
            bad.append(k)
        if worst is None or frac > worst[1]:
            worst = (k, frac)
        print(f"k={k:3d}  E_fk={float(E_fk.mid()):12.4f}  assembly=[{float(E_lo.lower()):10.2f},{float(E_hi.upper()):10.2f}]  "
              f"implied|E1|/allow={frac:.3f}  {'OK' if overlap else 'FAIL'}")
    print()
    if bad:
        print(f"*** {len(bad)} NON-OVERLAPS at k={bad} — assembly glue error, STOP and report ***")
    else:
        print(f"ALL k in [{klo},{khi}] overlap: assembly identity consistent with the independent f_k pipeline.")
        print(f"Tightest fit: k={worst[0]}, implied |E1|/allowance = {worst[1]:.3f} "
              f"(empirical check that the certified alpha ~ 15.57 is not violated in practice).")

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "certificate.json")

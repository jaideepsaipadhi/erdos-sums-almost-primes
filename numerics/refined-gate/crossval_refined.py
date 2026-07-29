"""Refined acceptance gate (run inside bm-rebuild-v21/ with the refinement files).

Tests the refined enclosure  E1(k) in M2(k) +/- Gamma  against the independent
f_k pipeline, for every k in [100,200]:

    implied-E1 interval  :=  core(k) - E_fk(k)        (assembly-certified core,
                                                       certificate-certified f_k)
    refined interval     :=  M2(k) +/- Gamma

The true E1(k) lies in BOTH (assembly identity, already validated 101/101), so
they MUST overlap at every k. Any non-overlap CONTRADICTS the refined
enclosure: in that case K0=79 is rejected and K0=735 (the proven fallback)
stands. Also reported: deviation ratio |mid(implied) - mid(M2)| / Gamma
(expected ~0.01 from remote checkpoints; anything approaching 1 is a red flag
even if overlapping).

Usage:
    python3 crossval_refined.py /workspace/certificate-k200.json

Requires in the working directory: ci_certified.{py,json}, tail_constants.json,
delta_table.jsonl, beta_certified.json (unused here but harmless),
m1_constant.json, bhat_signed_N60.json, gamma_constant.json, s2_table.py,
delta_conv.py.
"""
import sys, json, re
from flint import arb, ctx

def parse_ball(s):
    m = re.match(r"\[?(-?[0-9.]+(?:e[+-]?[0-9]+)?)(?: \+/- ([0-9.e+-]+))?\]?", s)
    a = arb(m.group(1)); r = arb(m.group(2) or "0")
    return a.union(a - r).union(a + r)

def load_fk(path):
    c = json.load(open(path))
    enc = c["enclosures"]
    out = {}
    for idx, rec in enumerate(enc):
        k = int(rec["k"]) if "k" in rec else idx + 1
        out[k] = (str(rec["f_k"][0]), str(rec["f_k"][1]))
    if 1 in out and not str(out[1][0]).startswith("1.14481657340591799"):
        raise RuntimeError("k-indexing wrong: k=1 record is " + str(out[1][0])[:25])
    print("load_fk: %d records, k range [%d, %d]" % (len(out), min(out), max(out)))
    return out

def main(cert_path, klo=100, khi=200, prec=800):
    ctx.prec = prec
    ci = {int(k): parse_ball(v) for k, v in json.load(open("ci_certified.json")).items()}
    tc = json.load(open("tail_constants.json"))
    rho = parse_ball(tc["rho"]); supH = arb(tc["supH_R4.2_upper"])
    delta = {}
    for line in open("delta_table.jsonl"):
        r = json.loads(line)
        mid = parse_ball(r["mid"]); rad = arb(r["rad"].strip("[]").split(" ")[0])
        delta[r["m"]] = mid.union(mid - rad).union(mid + rad)
    bhat = {int(k): parse_ball(v) for k, v in json.load(open("bhat_signed_N60.json")).items()}
    gc = json.load(open("gamma_constant.json"))
    Gamma = arb(str(gc["Gamma"]))
    M1 = arb(str(json.load(open("m1_constant.json"))["M1_R2.9"]))
    from ci_certified import certified_d
    from s2_table import A2
    ln2 = arb(2).log(); q = ln2 / 4
    d = certified_d(2000000, prec)
    a1 = d * q

    def coeff_ball(i):
        if i <= 30: return ci[i]
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
        for i in range(0, k + 1):
            s += arb(2) ** i * (ci[i] if i <= 30 else coeff_ball(i)) * delta[k - i]
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

    A2cache = {}
    def A2c(m):
        if m not in A2cache: A2cache[m] = A2(m, int(1.6 * m) + 200)
        return A2cache[m]

    def M2(k):
        s = arb(0)
        for i in range(1, min(60, k) + 1):
            s += bhat[i] * arb(2) ** i * A2c(k - i)
        r = arb(2) / arb("2.9")
        tail = M1 * (r ** 61) / (1 - r) * (arb(k + 1) / 2)
        return s.union(s - tail).union(s + tail)

    fk = load_fk(cert_path)
    bad = []; worst = (None, 0.0); tested = 0
    for k in range(klo, khi + 1):
        if k not in fk: continue
        tested += 1
        lo, hi = fk[k]
        f = arb(lo).union(arb(hi))
        E_fk = arb(2) ** k * (1 - f) - a1 * arb(k) ** 2
        core = -q * (2 * k * Uc[k] - Vc[k]) - Delta(k) + Eexp(k)
        implied = core - E_fk               # ball containing true E1(k)
        m2 = M2(k)
        ref_lo = float((m2 - Gamma).lower()); ref_hi = float((m2 + Gamma).upper())
        overlap = not (float(implied.upper()) < ref_lo or float(implied.lower()) > ref_hi)
        dev = abs(float(implied.mid()) - float(m2.mid())) / float(Gamma)
        if not overlap: bad.append(k)
        if dev > worst[1]: worst = (k, dev)
        print(f"k={k:3d}  implied E1 = {float(implied.mid()):8.3f}  M2 = {float(m2.mid()):8.3f}  "
              f"|dev|/Gamma = {dev:.4f}  {'OK' if overlap else 'FAIL'}")
    print()
    if bad:
        print(f"*** GATE FAILED at k={bad}: refined enclosure contradicted. "
              f"K0=79 REJECTED; K0=735 (fallback) stands. Report to Claude. ***")
    else:
        print(f"GATE PASSED: refined enclosure E1 in M2 +/- Gamma consistent at all "
              f"{tested} tested points. Worst deviation ratio {worst[1]:.4f} at k={worst[0]} "
              f"(expected ~0.01; Gamma = {float(Gamma):.2f}).")
        print("K0 = 79 (refined) is ACCEPTED pending the [810,899] slice completion.")

if __name__ == "__main__":
    main(sys.argv[1] if len(sys.argv) > 1 else "certificate.json")

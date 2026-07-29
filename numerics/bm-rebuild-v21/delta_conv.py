"""Certified Delta(k) = sum_{i=0}^k 2^i c_i delta_{k-i}, k <= 900.

Head i <= 30: certified c_i balls (ci_certified.json regenerated as arb).
Tail i > 30:  c_i in -rho/3^{i+1} +/- supH/R^i  (R=4.2), certified rho & supH.
delta: certified table m=0..900.

Validation: independent mpmath computation (FFT c_i to i=80 with primezeta
tails + series delta) must land inside the certified balls.
"""
from flint import arb, ctx
import json, re

def parse_ball(s):
    m = re.match(r"\[?(-?[0-9.]+(?:e[+-]?[0-9]+)?)(?: \+/- ([0-9.e+-]+))?\]?", s)
    mid = m.group(1); rad = m.group(2) or "0"
    a = arb(mid)
    r = arb(rad)
    return a.union(a - r).union(a + r)

def load_all(prec=400):
    ctx.prec = prec
    ci = {int(k): parse_ball(v) for k, v in json.load(open("ci_certified.json")).items()}
    tc = json.load(open("tail_constants.json"))
    rho = parse_ball(tc["rho"])
    supH = arb(tc["supH_R4.2_upper"])
    delta = {}
    for line in open("delta_table.jsonl"):
        r = json.loads(line)
        delta[r["m"]] = parse_ball(r["mid"]).union(parse_ball(r["mid"]) - arb(r["rad"].strip("[]").split(" ")[0])).union(parse_ball(r["mid"]) + arb(r["rad"].strip("[]").split(" ")[0]))
    return ci, rho, supH, delta

def Delta(k, ci, rho, supH, delta, N=30, R="4.2"):
    ctx_R = arb(R)
    s = arb(0)
    for i in range(0, min(N, k) + 1):
        s += arb(2) ** i * ci[i] * delta[k - i]
    for i in range(N + 1, k + 1):
        c_ball = -rho / arb(3) ** (i + 1)
        h = supH / ctx_R ** i
        c_ball = c_ball.union(c_ball - h).union(c_ball + h)
        s += arb(2) ** i * c_ball * delta[k - i]
    return s

if __name__ == "__main__":
    ci, rho, supH, delta = load_all()
    for k in [100, 400, 741, 900]:
        d = Delta(k, ci, rho, supH, delta)
        print(f"Delta({k}) = {d.str(12)}")

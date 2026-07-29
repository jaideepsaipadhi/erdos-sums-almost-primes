"""Certified enclosure of delta_m = A_m - 2^{m+1} + (log2/4) m^2, GLW Lemma 3.3.

A_m = sum_{i=0}^m (2^i/i!) J(i),  J(i)/i! = sum_{n>=0} (-a)^n / (n! (n+1)^{i+1}),
a = (m-i) log 2.

All arithmetic in Arb balls (python-flint). Truncation of the n-series is bounded
rigorously: for n0 with a/(n0+1) <= q < 1, |tail| <= |t_{n0}| / (1-q) since
|t_{n+1}/t_n| = (a/(n+1)) * ((n+1)/(n+2))^{i+1} <= a/(n+1) <= q for n >= n0.
The tail bound is added to the ball radius, so the returned arb CONTAINS delta_m.
"""
from flint import arb, ctx
import sys, time, json

def delta_arb(m, prec_bits):
    ctx.prec = prec_bits
    ln2 = arb(2).log()
    quarter_ln2 = ln2 / 4
    A = arb(0)
    two_i = arb(1)  # 2^i
    for i in range(m + 1):
        a = ln2 * (m - i)
        # series sum_n t_n, t_n = (-a)^n / (n! (n+1)^{i+1})
        s = arb(0)
        t = arb(1)  # t_0 = 1 / 1^{i+1} ... careful: t_n = (-a)^n/n! * (n+1)^{-(i+1)}
        # track c_n = (-a)^n / n! separately; t_n = c_n * (n+1)^{-(i+1)}
        c = arb(1)
        n = 0
        a_f = float(m - i) * 0.6931471805599453
        n_min = int(2 * a_f) + 20  # ensures a/(n+1) <= 1/2 beyond here
        import math
        log_c = 0.0  # log |c_n| = n log a - log n! (float estimate, only for loop control)
        while True:
            s += c * arb(n + 1) ** (-(i + 1))
            n += 1
            if a_f > 0:
                log_c += math.log(a_f) - math.log(n)
            else:
                log_c = -1e9
            c *= -a / n
            # stop when past ratio-1/2 point AND term is below 2^-(prec+40)
            if n >= n_min and log_c - (i + 1) * math.log(n + 1) < -(prec_bits + 40) * 0.6931471805599453:
                break
        # tail: first omitted term, geometric with ratio <= 1/2
        tail = abs(c) * arb(n + 1) ** (-(i + 1)) * 2
        s = s.union(s + tail).union(s - tail)
        A += two_i * s
        two_i *= 2
    return A - arb(2) ** (m + 1) + quarter_ln2 * arb(m) ** 2

if __name__ == "__main__":
    ms = [int(x) for x in sys.argv[1:]]
    prec = 1800
    out = {}
    for m in ms:
        t0 = time.time()
        d = delta_arb(m, prec)
        mid, rad = d.mid(), d.rad()
        out[m] = {"mid": str(mid.str(25)), "rad": str(rad.str(5))}
        print(f"m={m:5d}  delta = {d.str(22)}   ({time.time()-t0:.0f}s)", flush=True)
    json.dump(out, open("/home/claude/delta_arb.json", "w"), indent=1)

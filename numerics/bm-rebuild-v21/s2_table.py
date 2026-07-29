"""Certified S2(m) = 2^-m A2_m,  A2_m = 2^m sum_{j+l=m} int_1^2 ((-log(s-1))^l/l!)(s-1) 2^{-js} ds.
Substituting s=1+e^{-t}:  A2_m = sum_{j+l=m} 2^l * J2(l,j)/l!,
  J2(l,j)/l! = sum_n (-a)^n / (n! (n+2)^{l+1}),  a = j log2
(expand 2^{-j e^{-t}}; int t^l e^{-(n+2)t} dt = l!/(n+2)^{l+1}).
Truncation: |t_{n+1}/t_n| = a/(n+1) * ((n+2)/(n+3))^{l+1} <= a/(n+1) <= 1/2 for n >= 2a-1;
tail <= 2|first omitted| exactly as the delta series lemma."""
from flint import arb, ctx
import math, json, sys

def A2(m, prec):
    ctx.prec = prec
    ln2 = arb(2).log()
    tot = arb(0)
    for j in range(m + 1):
        l = m - j
        a = ln2 * j
        a_f = j * 0.6931471805599453
        s = arb(0); c = arb(1); n = 0
        n_min = int(2 * a_f) + 20
        log_c = 0.0
        while True:
            s += c * arb(n + 2) ** (-(l + 1))
            n += 1
            log_c += (math.log(a_f) - math.log(n)) if a_f > 0 else -1e9
            c *= -a / n
            if n >= n_min and log_c - (l + 1) * math.log(n + 2) < -(prec + 40) * 0.6931471805599453:
                break
        tail = abs(c) * arb(n + 2) ** (-(l + 1)) * 2
        s = s.union(s - tail).union(s + tail)
        tot += arb(2) ** l * s
    return tot

def S2(m, prec):
    return A2(m, prec) / arb(2) ** m

if __name__ == "__main__":
    for m in [int(x) for x in sys.argv[1:]]:
        print(f"S2({m}) = {S2(m, int(1.6*m)+200).str(20)}")

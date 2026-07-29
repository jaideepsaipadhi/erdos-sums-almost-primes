"""Reference implementation of GLW Lemma 3.3 quantities, straight from the paper.

A_m := sum_{i=0}^m (2^i / i!) * J(i, m),
J(i, m) := int_0^inf u^i e^{-u} 2^{-(m-i) e^{-u}} du,
delta_m := A_m - 2^{m+1} + (log2/4) m^2.

Uncertified (mpmath quadrature), used as ground truth for the certified rebuild.
"""
import mpmath as mp
import sys, json

def J(i, m, dps):
    mp.mp.dps = dps
    c = mp.mpf(m - i)
    ln2 = mp.log(2)
    # integrand: u^i e^{-u} exp(-c ln2 e^{-u})
    f = lambda u: mp.exp(i * mp.log(u) - u - c * ln2 * mp.exp(-u)) if u > 0 else (mp.mpf(1) if i == 0 else mp.mpf(0))
    # peak of u^i e^{-u} near u=i; split integration for stability
    pts = [0, max(i, 1), max(i, 1) + 60 + i]
    val = mp.quad(f, pts)
    # tail beyond last point: u^i e^{-u} <= e^{-u/2} * (u^i e^{-u/2}), crude but tiny
    return val

def A(m, dps):
    mp.mp.dps = dps
    s = mp.mpf(0)
    for i in range(m + 1):
        s += mp.mpf(2)**i / mp.factorial(i) * J(i, m, dps)
    return s

def delta(m, dps=60):
    mp.mp.dps = dps
    return A(m, dps) - mp.mpf(2)**(m + 1) + mp.log(2)/4 * mp.mpf(m)**2

if __name__ == "__main__":
    ms = [int(x) for x in sys.argv[1:]] or [10, 20, 30, 40, 60]
    out = {}
    for m in ms:
        d = delta(m, dps=60)
        out[m] = mp.nstr(d, 20)
        print(f"m={m:5d}  delta_m = {mp.nstr(d, 20)}")
    with open("/home/claude/delta_ref.json", "w") as fh:
        json.dump(out, fh, indent=1)

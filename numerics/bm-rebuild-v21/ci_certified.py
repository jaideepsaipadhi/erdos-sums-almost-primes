"""Certified coefficients c_i = [z^i] G_2(1,z), where
G_2(1,z) = (1 - z/2) G(1,z) = 2^{-z} prod_{p>2} (1-z/p)^{-1} (1-1/p)^z.

log G_2(1,z) = l_1 z + sum_{j>=2} l_j z^j,
  l_1 = -log2 + sum_{p>2} [log(1-1/p) + 1/p]          (absolutely convergent)
  l_j = P(j)/j,  P(j) = sum_{p>2} p^{-j}               (j >= 2)

Prime tails (p > P), certified:
  |sum_{p>P} [log(1-1/p)+1/p]| <= (1/(2(1-1/P))) * sum_{n>P} n^{-2}
                                <= 0.51/(P-1)                       (for P>=100)
  0 <= sum_{p>P} p^{-j} <= int_P^inf t^{-j} dt = P^{1-j}/(j-1)

exp recurrence: c_0 = 1, c_n = (1/n) sum_{j=1}^{n} j l_j c_{n-j}.
Since exp(L_N + R) = exp(L_N)(1 + O(z^{N+1})) when R has valuation > N,
coefficients c_0..c_N from the truncated log-series are EXACT modulo the
ball radii of the l_j. No separate truncation error.

Also certifies d = G_2(1,2) = (1/4) prod_{p>2} (1-2/p)^{-1}(1-1/p)^2 for the
identity check, with tail sum_{p>P} sum_j (2^j-2)/(j p^j) <= 3/P for P >= 8.
"""
from flint import arb, ctx
import json

def sieve(P):
    bs = bytearray([1]) * 0  # placeholder
    is_c = bytearray([0]) * (P + 1)
    primes = []
    for n in range(2, P + 1):
        if not is_c[n]:
            primes.append(n)
            for m in range(n * n, P + 1, n):
                is_c[m] = 1
    return primes

def interval(lo, hi):
    mid = (lo + hi) / 2
    return mid.union(lo).union(hi)

def certified_ci(N, P, prec):
    ctx.prec = prec
    primes = [p for p in sieve(P) if p > 2]
    ln2 = arb(2).log()

    # certified tail of sum_{p>P} p^-2 via Rosser-Schoenfeld pi(x) < 1.26 x/log x (x>=17):
    # sum_{p>P} p^-2 = int_P^inf t^-2 dpi(t) <= 2*1.26 int_P^inf dt/(t^2 log t) <= 2.52/(P log P)
    tailP2 = arb("2.52") / (arb(P) * arb(P).log())

    # l_1
    s1 = arb(0)
    for p in primes:
        pp = arb(p)
        s1 += (1 - 1 / pp).log() + 1 / pp
    tail1 = arb("0.51") * tailP2   # |log(1-x)+x| <= 0.51 x^2 for x <= 1/P
    l = [arb(0), -ln2 + s1 + interval(-tail1, tail1)]

    # l_j, j = 2..N
    # P(j) head via powers: keep p^{-j} running
    inv = [arb(1) / p for p in primes]
    cur = [x * x for x in inv]  # p^{-2}
    for j in range(2, N + 1):
        head = arb(0)
        for t in cur:
            head += t
        tail = tailP2 * arb(P) ** (2 - j)   # sum_{p>P} p^-j <= (sum p^-2) P^{2-j}
        Pj = head + interval(arb(0), tail)
        l.append(Pj / j)
        cur = [cur[t] * inv[t] for t in range(len(cur))]

    # exp recurrence
    c = [arb(1)]
    for n in range(1, N + 1):
        acc = arb(0)
        for j in range(1, n + 1):
            acc += j * l[j] * c[n - j]
        c.append(acc / n)
    return c

def certified_d(P, prec):
    ctx.prec = prec
    primes = [p for p in sieve(P) if p > 2]
    s = arb(0)
    for p in primes:
        pp = arb(p)
        s += -(1 - 2 / pp).log() + 2 * (1 - 1 / pp).log()
    # sum_{p>P} sum_j (2^j-2)/(j p^j) = sum_{p>P} (1/p^2 + 2/p^3 + ...) <= 1.01 sum_{p>P} p^-2
    primes2 = primes  # noqa
    tail = arb("1.01") * arb("2.52") / (arb(P) * arb(P).log())
    return (interval(s - tail, s + tail)).exp() / 4

if __name__ == "__main__":
    N, P, prec = 30, 2000000, 400
    c = certified_ci(N, P, prec)
    d = certified_d(P, prec)
    print("d =", d.str(12), "   (published: 0.3786950 +/- 4e-7)")
    for i in range(0, 15):
        print(f"c_{i:2d} = {c[i].str(15)}")
    json.dump({i: c[i].str(20) for i in range(N + 1)}, open("ci_certified.json", "w"), indent=1)
    # consistency: sum c_i = G_2(1,1) = 1/2 (converges like 3^-i)
    s = arb(0)
    for i in range(N + 1):
        s += c[i]
    print("sum c_i (head, ~3^-N tail) =", s.str(12), "  target 0.5")
    # consistency: sum c_i 2^i = d (converges like (2/3)^i, slow)
    s2 = arb(0)
    for i in range(N + 1):
        s2 += c[i] * arb(2) ** i
    print("sum c_i 2^i (head, ~(2/3)^N tail) =", s2.str(10), "  target d above")

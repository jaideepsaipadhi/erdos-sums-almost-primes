#!/usr/bin/env python3
"""Emit the Lean statement and data for a certified LOWER bound on dConst.

    dConst = (1/4) * prod_{p prime >= 3} (1 - 2/p)^-1 (1 - 1/p)^2
           = (1/4) * prod_{p prime >= 3} (1 + 1/(p(p-2)))

the second form being exact:  (1-2/p)^-1 (1-1/p)^2 = (p-1)^2/(p(p-2)).
Every factor exceeds 1, so the product over ANY finite set of primes is a
lower bound for the whole product -- no tail estimate is involved.  That is
the whole reason a lower bound is reachable in Lean while the two-sided
5.3e-8 enclosure is not.

A lower bound is all the development ever uses d for:

  unrestricted   aOneConst = dConst * log 2 / 4 >= 0.0656   (aOneConst_ge_of_d)
  odd            betaOdd = dConst*(log2 - Sodd + gamma) >= 0.1556

Both consume a lower bound on log 2 as well, and the Lean proofs use
Real.log_two_gt_d9, NOT the true value -- so the requirement on dConst must be
computed against 0.6931471803.  Computing it against the true log 2 understates
how many primes are needed (0.3785243 rather than 0.3785632, which is the
difference between 66 primes and 79).

Settings of record: N = 500 for the unrestricted bound (94 primes, margin
2.8e-5).  The odd bound needs N >= 5000 and has at most 1.27e-5 of margin
available at any N, because betaOdd's own slack caps it.

Usage: python3 gen_dconst_lower.py [N]
"""
import sys
sys.set_int_max_str_digits(200000)
from fractions import Fraction as F

def primes_upto(n):
    s = bytearray([1]) * n
    s[0:2] = b"\0\0"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i*i::i] = bytearray(len(s[i*i::i]))
    return [i for i in range(n) if s[i]]

N = int(sys.argv[1]) if len(sys.argv) > 1 else 500
ps = [p for p in primes_upto(N) if p >= 3]

P = F(1)
for p in ps:
    P *= 1 + F(1, p * (p - 2))
val = P / 4

log2lo = F(6931471803, 10 ** 10)              # Real.log_two_gt_d9
need_u = F(656, 10000) * 4 / log2lo           # aOneConst >= 0.0656
Sodd_hi = F(8593953, 10 ** 7) + F(33, 10 ** 7)
gam_lo = F(57715, 10 ** 5)
need_o = F(1556, 10000) / (log2lo - Sodd_hi + gam_lo)

# largest 7-decimal numeral strictly below the partial product
dec = (val * 10 ** 7).__floor__()
numeral = F(dec, 10 ** 7)

print("N = %d, %d primes, p <= %d" % (N, len(ps), ps[-1]))
print("partial/4           = %.12f" % float(val))
print("safe numeral        = %s" % numeral)
print("needed unrestricted = %.12f   margin %+.3e"
      % (float(need_u), float(val - need_u)))
print("needed odd          = %.12f   margin %+.3e"
      % (float(need_o), float(val - need_o)))
print("clears unrestricted : %s" % (numeral >= need_u))
print("clears odd          : %s" % (numeral >= need_o))
print()
print("-- Lean: the explicit prime set")
print("def dLowerPrimes : Finset ℕ :=")
body = ", ".join(str(p) for p in ps)
print("  {" + body + "}")
print()
print("-- Lean: the target")
print("theorem dConst_lower_bound : (%s : ℝ) ≤ dConst := by" % numeral)
print("  sorry  -- proof assembled separately; this script supplies the numeral")

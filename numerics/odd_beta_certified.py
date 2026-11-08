#!/usr/bin/env python3
"""Certify beta > 0 and the odd base case eq:odd-base-59 in ball arithmetic.

WHY THIS SCRIPT EXISTS
----------------------
Proposition 3.5(iv) asserts two things as certified: beta > 0, and

    4900 * 62^3 * 3^-59  <  (beta/3) * 2^-59.                  eq:odd-base-59

Both reduce to an upper bound on

    S = sum_{p>=3} log p / ((p-1)(p-2)),      beta = d (gamma + log 2 - S),

and until this script existed nothing in the repository certified S.  Its
numeral lived in ONE sentence of the manuscript's formalization section -- the
one that explained why S had to stay a Lean hypothesis -- and
check_proof_spine.py read it back out of the manuscript to derive beta and
re-check the base case.  So the base case was checked against a number the
paper asserted about itself, which is the same provenance defect that 101.245
and 1.45 had (see CLAUDE.md).  Removing the formalization section from the
paper removed the sentence, the guard failed, and the gap surfaced.

Everything here is one-sided in the safe direction, so no two-sided enclosure
of either constant is needed:

  * d = (1/4) prod_{p>=3} (1-2/p)^-1 (1-1/p)^2, and each factor is
        (p-1)^2 / (p(p-2)) = 1 + 1/(p(p-2))  >  1,
    so the partial product over p <= PCUT is a rigorous LOWER bound on d with
    no tail estimate at all.  This is the device the manuscript records for d.

  * For S an UPPER bound is needed, so the tail cannot be dropped.  Every term
    is positive and log p/((p-1)(p-2)) <= log p/(p-2)^2, so summing over all
    integers rather than only primes (safe for an upper bound) and comparing
    with an integral, with A = PCUT - 2 and log(u+2) <= log u + 2/u,

        sum_{p > PCUT} log p/((p-1)(p-2))
          <= int_A^inf (log u + 2/u)/u^2 du = (log A + 1)/A + 1/A^2.

    At PCUT = 10^8 that tail is below 2e-7.  The base case has percent-level
    margin and does not care, but Corollary 7.3 prints beta/d = 0.410970...,
    a truncation, so backing its sixth decimal needs the tail below about
    7e-7: at PCUT = 10^7 the certified lower bound is 0.4109690 and does NOT
    establish the printed value.  That is slack in this bound, not a
    disagreement with the paper -- the true tail is far smaller -- but a
    certificate has to establish what is printed, so PCUT is set accordingly.

Then beta >= d_lo * (gamma + log 2 - S_hi), both factors positive, and the
base case is checked from that.  Also printed: beta/d against the 0.410970...
of Corollary 7.3, and d against the 0.3786949 of Proposition 5.8, so this
script cross-checks the two places the manuscript prints these constants.

NAME COLLISION, DELIBERATELY AVOIDED: numerics/beta_certified.json is a
DIFFERENT beta -- the per-i coefficient bounds beta_i that beta_sweep.py
produces for alpha_+.  It has nothing to do with the beta of
eq:beta-intro certified here.  Hence the odd_ prefix; do not "tidy" it away.

    python3 odd_beta_certified.py            # -> odd_beta.log, about 20 s
    python3 odd_beta_certified.py 10000000   # faster; too loose for beta/d
"""
import sys
from flint import arb, ctx

ctx.prec = 300
PCUT = int(sys.argv[1]) if len(sys.argv) > 1 else 10 ** 8

# what the manuscript prints, and what this script must support
D_PAPER = arb("0.3786949")        # eq:full-certified-constants, d >= this
BETA_OVER_D_PAPER = arb("0.410970")   # Corollary 7.3, beta/d = this...
MR = arb(4900)                    # eq:odd-intro-expansion


def primes_upto(n):
    sieve = bytearray([1]) * (n + 1)
    sieve[0:2] = b"\x00\x00"
    for i in range(2, int(n ** 0.5) + 1):
        if sieve[i]:
            sieve[i * i::i] = bytearray(len(sieve[i * i::i]))
    return sieve


print("# primes 3..%d, prec = %d bits" % (PCUT, ctx.prec))
sieve = primes_upto(PCUT)

# ---------------------------------------------------------------- d, below
# Each factor exceeds 1, so the partial product is a lower bound: no tail.
# The sieve is walked in place rather than materialized as a list: at
# PCUT = 10^8 there are 5.76 million terms.
d_lo = arb(1) / 4
S_partial = arb(0)
nprimes = 0
for p in range(3, PCUT + 1, 2):
    if not sieve[p]:
        continue
    nprimes += 1
    pa = arb(p)
    d_lo *= 1 + 1 / (pa * (pa - 2))
    S_partial += pa.log() / ((pa - 1) * (pa - 2))
print("# %d odd primes" % nprimes)

print("# d >= %s   (partial product, every factor > 1, no tail needed)"
      % d_lo.lower().str(12))

# ---------------------------------------------------------------- S, above
A = arb(PCUT) - 2
S_tail = (A.log() + 1) / A + 1 / (A * A)
S_hi = S_partial + S_tail
print("# S  = %s + tail <= %s   (tail <= %s)"
      % (S_partial.upper().str(12), S_hi.upper().str(12),
         S_tail.upper().str(4)))

# ---------------------------------------------------------------- beta
log2 = arb(2).log()
gam = arb.const_euler() if hasattr(arb, "const_euler") else \
    arb("0.57721566490153286060651209008240243104")
bod_lo = gam + log2 - S_hi          # = beta/d, from below
beta_lo = d_lo * bod_lo

print()
print("beta/d = gamma + log2 - S >= %s" % bod_lo.lower().str(12))
print("beta                      >= %s" % beta_lo.lower().str(12))

# ---------------------------------------------------------------- checks
fails = []


def check(label, ok, detail):
    print("%-52s %s" % (label, "ok" if ok else "FAIL"))
    print("    %s" % detail)
    if not ok:
        fails.append(label)


print()
check("beta > 0  (Proposition 3.5(iv), first half)",
      float(beta_lo.lower()) > 0,
      "beta >= %.10f" % float(beta_lo.lower()))

# eq:odd-base-59:  MR * 62^3 * 3^-59  <  (beta/3) * 2^-59
lhs = MR * arb(62) ** 3 * arb(3) ** (-59)
rhs = beta_lo / 3 * arb(2) ** (-59)
check("eq:odd-base-59, the k = 59 base case",
      float(lhs.upper()) < float(rhs.lower()),
      "LHS <= %.6e, RHS >= %.6e, margin %.2f%%"
      % (float(lhs.upper()), float(rhs.lower()),
         100 * (1 - float(lhs.upper()) / float(rhs.lower()))))

# the manuscript's two printed numerals, each checked in its own direction
check("d >= %s as Proposition 5.8 states" % D_PAPER.str(9, radius=False),
      float(d_lo.lower()) >= float(D_PAPER.str(20, radius=False)),
      "certified d >= %.10f, stated %s"
      % (float(d_lo.lower()), D_PAPER.str(9, radius=False)))

# Corollary 7.3 prints beta/d = 0.410970... as a truncation, so the certified
# value must lie in [0.410970, 0.410971).
check("beta/d = %s... as Corollary 7.3 prints"
      % BETA_OVER_D_PAPER.str(8, radius=False),
      float(bod_lo.lower()) >= float(BETA_OVER_D_PAPER.str(20, radius=False))
      and float(bod_lo.upper()) < float(BETA_OVER_D_PAPER.str(20,
                                                             radius=False))
      + 1e-6,
      "certified beta/d in [%.10f, %.10f]"
      % (float(bod_lo.lower()), float(bod_lo.upper())))

print()
if fails:
    print("FAILURES: %s" % ", ".join(fails))
    sys.exit(1)
print("beta > 0 and the k = 59 base case are certified from S and d, both")
print("bounded one-sidedly in the safe direction.  check_proof_spine.py reads")
print("beta from this log, not from the manuscript.")
sys.exit(0)

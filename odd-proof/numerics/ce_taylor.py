#!/usr/bin/env python3
"""Interval-certified CE over the WHOLE range s in (1, sOf(3)], u >= 3.

The four constants of oddTerm_bound are ratios in which zeta's pole at s = 1
cancels.  Evaluating them on boxes of s fails: arb treats each occurrence of
(s-1) independently and the cancellation is lost (the dependency problem), so
enclosures blow up however narrow the boxes.

The fix is a Taylor model.  Expanding zeta as an arb power series about
s0 = 1 + E/2 (E = sOf(3) - 1) and forming the constants as series makes the
cancellation SYMBOLIC; the resulting series have small, decaying coefficients
and evaluate tightly on |delta| <= E/2, which is the whole range at once.
No monotonicity in s is assumed.

TRUNCATION.  python-flint's arb_series.zeta() returns 9-10 terms regardless of
the requested length, so the series here are degree <= 9 and the ORDER argument
below has no effect (kept for the call signature).  That is far more than
enough: the coefficients of Cf decay by a factor of about ten per order and the
implied radius of convergence is ~11.6, so with |delta| <= E/2 = 0.0256 the
terms fall by ~400x per order --

    n:      6          7          8
    |c|d^n  1.27e-13   3.28e-16   7.24e-19

and the discarded tail beyond n = 8 is geometric with ratio delta/11.6 =
0.0022, i.e. about 1.6e-21.  The bound below is therefore safe by twenty
orders of magnitude.  The `tail` term in ev() covers the last three COMPUTED
coefficients; the analytic remainder past them is the 1.6e-21 just given.

Usage: python3 ce_taylor.py [ORDER-ignored] [PREC]
"""
import sys
from flint import arb, ctx, arb_series

M    = int(sys.argv[1]) if len(sys.argv) > 1 else 25
PREC = int(sys.argv[2]) if len(sys.argv) > 2 else 300
ctx.prec = PREC

E  = arb('0.0512699547949')          # sOf(3) - 1
s0 = 1 + E / 2
z  = arb_series([s0, 1], M).zeta()
zp = z.derivative()
eps = arb_series([s0 - 1, 1], M)
g  = arb.const_euler()
J  = z / (-zp)

Cb = eps * z
Cf = (J - z.inv()) * z * z
CJ = (J - z.inv() - 2*g*z.inv()*z.inv()) * z * z * z
CP = (eps*J - z.inv()*z.inv()) * z * z * z

d = arb(0).union(E/2).union(-E/2)

def ev(ser):
    cs = ser.coeffs()
    val, dp = arb(0), arb(1)
    for c in cs[:-3]:
        val += c * dp
        dp = dp * d
    tail = sum(abs(c) * abs(d)**(len(cs)-3+i) for i, c in enumerate(cs[-3:]))
    return (val + arb(0).union(tail).union(-tail)).upper()

b, f, jj, p = ev(Cb), ev(Cf), ev(CJ), ev(CP)
print(f"range: s in (1, 1+{E}],  expansion at s0 = 1 + E/2, order {M}")
print(f"  Cb <= {b}")
print(f"  Cf <= {f}")
print(f"  CJ <= {jj}")
print(f"  CP <= {p}")
CE = jj + p + b*b*(f + 1)
print(f"\nCE <= {CE}")

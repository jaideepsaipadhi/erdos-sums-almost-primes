#!/usr/bin/env python3
"""Guard the three-way correspondence for the PROVED d bounds.

CLAUDE.md requires every certified constant to agree in paper/proof.tex, in
the numerics, and in the Lean structures.  The d bounds are now a new kind of
entry: they are not assumed in Lean any more, they are PROVED there, which
creates two drift risks the old rule did not cover.

  1. A Lean numeral could claim more than is true -- the partial product over
     the committed prime set must actually reach it.  Round the wrong way and
     the theorem is false, not merely weak.  This is the S* <= 6.9763 failure
     mode, and it already happened once here: 0.3786822 was truncated from a
     requirement of 0.378682252653.
  2. A Lean numeral could be too weak for its consumer.  The requirements are
     computed against the bounds the Lean proofs HAVE -- Real.log_two_gt_d9's
     0.6931471803, Sodd at 0.8593986, gamma at 0.57715 -- not against the true
     constants.  Using true log 2 understates the needed prime count, which is
     how a 66-prime version of dConst_lower_bound came to be written.

This script reads the numerals out of the Lean sources rather than taking them
on faith, recomputes the partial products, and checks both directions.

Exit status is nonzero if any check fails.  Usage: python3 check_lean_constants.py
"""
import re
import sys
sys.set_int_max_str_digits(400000)
from fractions import Fraction as F
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

LOG2_LO = F(6931471803, 10 ** 10)        # Real.log_two_gt_d9
SODD_HI = F(8593953, 10 ** 7) + F(33, 10 ** 7)   # Sodd_enclosure, worst end
GAMMA_LO = F(57715, 10 ** 5)             # Odd.gamma_lower_bound
A_ONE_TARGET = F(656, 10000)             # aOneConst_ge
BETA_TARGET = F(1556, 10000)             # betaOdd >= 0.1556
PAPER_D_LO = F(3786949, 10 ** 7)         # paper/proof.tex, prop:full-certified


def primes_upto(n):
    s = bytearray([1]) * n
    s[0:2] = b"\0\0"
    for i in range(2, int(n ** 0.5) + 1):
        if s[i]:
            s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(n) if s[i]]


def read_lean(rel):
    p = ROOT / rel
    return p.read_text() if p.exists() else ""


def numeral_of(src, name):
    """The numeral in `theorem <name> : (X : R) <= dConst`."""
    m = re.search(re.escape(name) + r"\s*:\s*\(([0-9.]+)\s*:", src)
    return F(m.group(1)) if m else None


def primes_of(src, defname):
    """The prime set in `def <defname> ... { 3, 5, ... }`."""
    m = re.search(r"def\s+" + re.escape(defname) + r"[^=]*:=\s*\{(.*?)\}", src, re.S)
    if not m:
        return None
    return [int(x) for x in re.findall(r"⟨(\d+),", m.group(1))]


def partial_over(ps):
    P = F(1)
    for p in ps:
        P *= 1 + F(1, p * (p - 2))
    return P / 4


bm = read_lean("Banksmartin/Basic.lean")
odd = read_lean("Odd/Basic.lean")
fails = []


def check(label, ok, detail):
    print("%-58s %s" % (label, "ok" if ok else "FAIL"))
    print("    %s" % detail)
    if not ok:
        fails.append(label)


# --- the factor identity the whole approach rests on, verified numerically
bad = [p for p in primes_upto(2000) if p >= 3
       and (1 - F(2, p)) ** -1 * (1 - F(1, p)) ** 2 != 1 + F(1, p * (p - 2))]
check("Euler factor identity (1-2/p)^-1(1-1/p)^2 = 1+1/(p(p-2))",
      not bad, "exact for every prime 3 <= p < 2000" if not bad else "fails at %s" % bad[:3])

# --- the unrestricted bound
num = numeral_of(bm, "dConst_lower_bound")
ps = primes_of(bm, "dLowerSet")
if num is None or ps is None:
    check("dConst_lower_bound present", False, "could not parse numeral or prime set")
else:
    prod = partial_over(ps)
    need = A_ONE_TARGET * 4 / LOG2_LO
    check("dConst_lower_bound numeral is actually reached",
          num <= prod,
          "numeral %s <= partial product %.12f over %d primes (p <= %d)"
          % (num, float(prod), len(ps), max(ps)))
    check("dConst_lower_bound suffices for aOneConst >= 0.0656",
          num >= need,
          "numeral %.12f >= required %.12f (margin %+.3e)"
          % (float(num), float(need), float(num - need)))
    check("every member of dLowerSet is prime and >= 3",
          all(p >= 3 and p in set(primes_upto(max(ps) + 1)) for p in ps),
          "%d entries checked" % len(ps))
    check("dConst_lower_bound is consistent with the paper's d >= 0.3786949",
          num <= PAPER_D_LO,
          "Lean proves %s, weaker than the paper's certified %s -- no conflict"
          % (num, PAPER_D_LO))

# --- the odd bound, if it is present as a theorem
sharp = numeral_of(bm, "dConst_lower_bound_sharp")
sps = primes_of(bm, "dLowerSetSharp")
fac = LOG2_LO - SODD_HI + GAMMA_LO
need_odd = BETA_TARGET / fac
if sharp is not None and sps is not None:
    sprod = partial_over(sps)
    check("dConst_lower_bound_sharp numeral is actually reached",
          sharp <= sprod,
          "numeral %s <= partial product %.12f over %d primes (p <= %d)"
          % (sharp, float(sprod), len(sps), max(sps)))
    check("dConst_lower_bound_sharp suffices for betaOdd >= 0.1556",
          sharp >= need_odd,
          "numeral %.12f >= required %.12f (margin %+.3e); note 0.3786822 FAILS here"
          % (float(sharp), float(need_odd), float(sharp - need_odd)))
    check("dConst_lower_bound_sharp consistent with the paper",
          sharp <= PAPER_D_LO,
          "Lean proves %s, weaker than the paper's %s" % (sharp, PAPER_D_LO))
else:
    print("%-58s %s" % ("dConst_lower_bound_sharp", "absent"))
    print("    the odd side assumes d rather than proving it; checking the field")
    m = re.search(r"d_lower\s*:\s*\(([0-9.]+)\s*:", odd)
    if m:
        v = F(m.group(1))
        check("OddNumericalFacts.d_lower suffices for betaOdd >= 0.1556",
              v >= need_odd,
              "field %.12f >= required %.12f (margin %+.3e)"
              % (float(v), float(need_odd), float(v - need_odd)))
        check("OddNumericalFacts.d_lower is true (below the real d)",
              v <= PAPER_D_LO,
              "field %s <= paper's certified %s" % (v, PAPER_D_LO))

# --- rho: same shape, opposite sign, and no consumer
rnum = None
m = re.search(r"rhoConst_upper_bound\s*:\s*rhoConst\s*≤\s*\((-?[0-9.]+)\s*:", bm)
if m:
    rnum = F(m.group(1))
rps = primes_of(bm, "rhoLowerSet")
if rnum is not None and rps is not None:
    RP = F(1)
    for p in rps:
        RP *= 1 + F(3 * p - 1, p * p * (p - 3))
    rub = -F(1, 9) * RP
    check("rhoConst_upper_bound numeral is actually reached",
          rnum >= rub,
          "numeral %.10f >= product bound %.10f over %d primes (p <= %d); "
          "an upper bound on a NEGATIVE quantity rounds TOWARD ZERO"
          % (float(rnum), float(rub), len(rps), max(rps)))
    check("rhoLowerSet members are prime and >= 5",
          all(p >= 5 and p in set(primes_upto(max(rps) + 1)) for p in rps),
          "%d entries checked" % len(rps))
    check("rhoConst_upper_bound is consistent with the paper's -0.1749323",
          rnum >= F(-1749323, 10 ** 7),
          "Lean proves rhoConst <= %.10f, weaker than the certified "
          "-0.1749323 -- no conflict" % float(rnum))

# --- the LOOSER Lean numerals: direction, and that they still suffice.
# alpha_bound and V_bound carry short-decimal rationals a hair above the
# certified values.  Looser is safe, TIGHTER would be a false hypothesis that
# no instance could satisfy -- and since no instance of the structure is ever
# constructed, a too-tight field would make the theorems vacuous rather than
# refutable.  So the direction is the thing to check.
print()
LEAN_SRC = (ROOT / "Banksmartin" / "Basic.lean").read_text()
TEX_SRC = (ROOT / "paper" / "proof.tex").read_text()
for name, pat_lean, pat_tex, label in (
        ("alpha_bound", r"\(hal *: *alph *(?:\u2264|<=) *([0-9.]+)\)",
         r"\\alpha_\+\\leq([0-9]+\.[0-9]+)", "alpha_+"),
        ("V_bound", r"\(hV *: *Vmax *(?:\u2264|<=) *([0-9.]+)\)",
         r"V_\{\\max\}=([0-9]+\.[0-9]+)", "V_max")):
    ml = re.search(pat_lean, LEAN_SRC)
    mt = re.search(pat_tex, TEX_SRC)
    if ml and mt:
        lv, tv = F(ml.group(1)), F(mt.group(1))
        check("%s: Lean numeral %s is >= the certified %s (looser, safe)"
              % (name, ml.group(1), mt.group(1)),
              lv >= tv,
              "Lean %.8f vs paper %.8f, slack %.2e"
              % (float(lv), float(tv), float(lv - tv)))
    else:
        check("%s: both numerals are parseable" % name, False,
              "Lean %s / paper %s -- guard would be vacuous"
              % (bool(ml), bool(mt)))

# --- what the consumers need, restated so a reader can see the budget
print()
print("requirement budget, against the bounds the LEAN PROOFS have:")
print("  log 2    >= %s   (Real.log_two_gt_d9, not the true log 2)" % LOG2_LO)
print("  Sodd     <= %s   (Sodd_enclosure, worst end)" % SODD_HI)
print("  gamma    >= %s      (Odd.gamma_lower_bound)" % GAMMA_LO)
print("  => aOneConst >= 0.0656 needs d >= %.12f" % float(A_ONE_TARGET * 4 / LOG2_LO))
print("  => betaOdd   >= 0.1556 needs d >= %.12f" % float(need_odd))
print()
if fails:
    print("FAILED: %d check(s): %s" % (len(fails), ", ".join(fails)))
    sys.exit(1)
print("all checks pass")

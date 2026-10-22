#!/usr/bin/env python3
"""Guard the phi(2440) substitution in Lemma phi-base against drift.

check_lean_constants.py guards the constants that appear in BOTH the Lean
structures and the paper.  The five substitutions inside Lemma phi-base are
not in that net: they are arithmetic performed only in the manuscript, and
the Lean side proves just `0 < phiBound`, so a loose intermediate numeral is
invisible to it.  One was in fact wrong --
`S^*(2D(2440)+D(2441)) < 276163.2` needed `S^* <= 6.97630949` while
eq:full-certified-constants gives `6.9764` -- and the two conclusions that
subtract it inherited the error.

The trap this script exists to prevent is subtler than a typo.  The Lean
numerals are deliberately rounded AWAY from the paper's (alpha_+ is 15.4257
in Lean against 15.425661 in the paper, V_max is 1.90747 against 1.907462),
so checking the paper's arithmetic against the Lean constants gives wrong
answers in both directions: it can condemn a correct bound and bless an
incorrect one.  I did exactly that once.  So this script reads the constants
out of paper/proof.tex -- not out of the Lean sources, and not from
hardcoded copies -- and recomputes with arb.

Everything is an interval: a claim of the form `X < c` is checked against
X.upper(), and `X > c` against X.lower().  str(arb) is never used for a
decision, since it rounds the midpoint and inflates the radius.

Scope has since widened past phi(2440): it also guards Lemma phi-monotone
(whose 2a_1 > 0.1312 and subtracted-term bounds carry the tightest margins in
the paper, 4.6e-5 and 6.0e-5, so they break before anything else if d or S^*
moves), the tail-coefficient constant C = 354.36, and the second-tail bound
Sigma_1 + 4 gamma Sigma_0 < 590.  Thirteen claims in total.

Exit status is nonzero if any check fails.
    Usage: python3 check_paper_phi.py
"""
import re
import sys
from pathlib import Path

try:
    from flint import arb, ctx
except ImportError:
    sys.exit("needs python-flint: pip install python-flint "
             "(--break-system-packages on this image)")

ctx.dps = 40

ROOT = Path(__file__).resolve().parent.parent
TEX = (ROOT / "paper" / "proof.tex").read_text()

fails = []


def check(label, ok, detail):
    print("%-54s %s" % (label, "ok" if ok else "FAIL"))
    print("    %s" % detail)
    if not ok:
        fails.append(label)


def grab(pattern, what):
    """Pull one decimal numeral out of the manuscript, or die loudly."""
    m = re.search(pattern, TEX)
    if not m:
        sys.exit("could not find %s in paper/proof.tex -- pattern %r.\n"
                 "If the manuscript was reworded, update the pattern; do NOT "
                 "hardcode the value, which is the whole point of this script."
                 % (what, pattern))
    return arb(m.group(1))


# --- the certified inputs, read from eq:full-certified-constants
d = grab(r"d\\geq([0-9]+(?:\.[0-9]+)?)", "the certified lower bound for d")
Sstar = grab(r"S\^\*\\leq([0-9]+(?:\.[0-9]+)?)", "the certified upper bound for S^*")
alph = grab(r"\\alpha_\+\\leq([0-9]+(?:\.[0-9]+)?)", "the certified upper bound for alpha_+")
Umax = grab(r"U_\{\\max\}=([0-9]+(?:\.[0-9]+)?)", "U_max")
Vmax = grab(r"V_\{\\max\}=([0-9]+(?:\.[0-9]+)?)", "V_max")

log2 = arb(2).log()
a1_lo = d * log2 / 4          # a_1 = d log2 / 4, and d is a LOWER bound


def D_hi(m):
    """D(m) = (log2) m log(m+1) + 1, as an upper bound."""
    return log2 * m * arb(m + 1).log() + 1


def R_hi(k):
    """R(k) of eq:R-def, as an upper bound: every input is used at its
    worst end, so this over-estimates R and hence under-estimates phi."""
    return (log2 / 4 * ((2 * k - 2) * Umax + 2 * Vmax + 4 * Umax)
            + Sstar * (2 * D_hi(k) + D_hi(k + 1))
            + alph * (3 * k + 4)
            + 3 * (arb("1.45") / k + arb("0.001")))


def phi_lo(k):
    return a1_lo * (k * k - 2 * k - 1) - R_hi(k)


print("certified inputs, as read from paper/proof.tex:")
for nm, v in (("d >=", d), ("S^* <=", Sstar), ("alpha_+ <=", alph),
              ("U_max =", Umax), ("V_max =", Vmax)):
    print("  %-10s %s" % (nm, v.str(12, radius=False)))
print()

# --- the five substitutions of Lemma phi-base, read from the manuscript
K = 2440
terms = [
    ("a1(k^2-2k-1)", a1_lo * (K * K - 2 * K - 1), ">",
     r"a_1\(2440\^2-2\\cdot2440-1\)&>([0-9]+(?:\.[0-9]+)?)"),
    ("term2 (Jacobian/U,V)", log2 / 4 * ((2 * K - 2) * Umax + 2 * Vmax + 4 * Umax), "<",
     r"\\bigl\(4878U_\{\\max\}\+2V_\{\\max\}\+4U_\{\\max\}\\bigr\)&<([0-9]+(?:\.[0-9]+)?)"),
    ("term3 (S^* delta-table)", Sstar * (2 * D_hi(K) + D_hi(K + 1)), "<",
     r"S\^\*\\bigl\(2D\(2440\)\+D\(2441\)\\bigr\)&<([0-9]+(?:\.[0-9]+)?)"),
    ("term4 (alpha_+)", alph * (3 * K + 4), "<",
     r"\\alpha_\+\(3\\cdot2440\+4\)&<([0-9]+(?:\.[0-9]+)?)"),
    ("term5 (E_exp)", 3 * (arb("1.45") / K + arb("0.001")), "<",
     r"3\\left\(\\frac\{1.45\}\{2440\}\+10\^\{-3\}\\right\)&<([0-9]+(?:\.[0-9]+)?)"),
]

for label, value, sense, pat in terms:
    claimed = grab(pat, "the claimed bound for " + label)
    c = float(claimed.str(20, radius=False))
    if sense == "<":
        ok = float(value.upper()) < c
        detail = "<= %.5f, claim < %.5f" % (float(value.upper()), c)
    else:
        ok = float(value.lower()) > c
        detail = ">= %.5f, claim > %.5f" % (float(value.lower()), c)
    check("%s %s %s" % (label, sense, claimed.str(10, radius=False)), ok, detail)

# --- Lemma phi-monotone.  Its three numerals carry the tightest margins in
# the paper -- 2a_1 > 0.1312 clears by 4.6e-5 and the subtracted term by
# 6e-5 -- so a change to d or S^* would break them before anything else.
print()
mono = [
    ("2a_1", 2 * a1_lo, ">", r"gives \$2a_1>([0-9]+(?:\.[0-9]+)?)\$"),
    ("S^* log2 (2/(x+2)+1/(x+3)) at x=2440",
     Sstar * log2 * (arb(2) / 2442 + arb(1) / 2443), "<",
     r"subtracted term is \$<([0-9]+(?:\.[0-9]+)?)\$ for"),
    ("M(2440)",
     a1_lo * (2 * 2440 - 1) - log2 / 2 * Umax - 3 * alph
     - Sstar * log2 * (2 * arb(2442).log() + arb(2443).log() + 3), ">",
     r"\$M\(2440\)>([0-9]+(?:\.[0-9]+)?)\$"),
]
for label, value, sense, pat in mono:
    claimed = grab(pat, "the claimed bound for " + label)
    c = float(claimed.str(20, radius=False))
    if sense == "<":
        ok, got = float(value.upper()) < c, float(value.upper())
    else:
        ok, got = float(value.lower()) > c, float(value.lower())
    check("%s %s %s" % (label, sense, claimed.str(10, radius=False)),
          ok, "actual %.8f, margin %.2e" % (got, abs(got - c)))

# --- two further substitutions elsewhere in the paper that use the same
# certified inputs, included so one command covers all of them.
print()
C = grab(r"With \$C=([0-9]+(?:\.[0-9]+)?)\$", "the tail-coefficient constant C")
sup = grab(r"\\abs\{\\widetilde G_2\(z\)\}\\leq([0-9]+(?:\.[0-9]+)?)\$", "the |z|=4.2 contour bound")
geo = sup * arb("4.2") / arb("1.2")        # sum_{m>=0} (3/4.2)^m = 4.2/1.2
check("C = %s covers sup * sum (3/4.2)^m" % C.str(10, radius=False),
      float(geo.upper()) <= float(C.str(20, radius=False)),
      "sup * 3.5 = %.6f" % float(geo.upper()))

S0 = grab(r"\\Sigma_0\\leq([0-9]+(?:\.[0-9]+)?)", "Sigma_0")
S1 = grab(r"\\Sigma_1\\leq([0-9]+(?:\.[0-9]+)?)", "Sigma_1")
gam = grab(r"[Ss]ince \$\\gamma<([0-9]+(?:\.[0-9]+)?)\$", "the gamma upper bound used")
b590 = grab(r"\\Sigma_1\+4\\gamma\\Sigma_0<([0-9]+(?:\.[0-9]+)?)", "the second-tail constant")
check("Sigma_1 + 4 gamma Sigma_0 < %s" % b590.str(10, radius=False),
      float((S1 + 4 * gam * S0).upper()) < float(b590.str(20, radius=False)),
      "actual %.6f" % float((S1 + 4 * gam * S0).upper()))

# --- the conclusion, and the sign change that fixes the threshold
concl = grab(r">390371.6-[0-9.]+-[0-9.]+-[0-9.]+-[0-9.]+>([0-9]+)\.", "the phi(2440) conclusion")
c = float(concl.str(20, radius=False))
check("phi(2440) > %s" % concl.str(10, radius=False),
      float(phi_lo(2440).lower()) > c,
      "phi(2440) >= %.4f" % float(phi_lo(2440).lower()))

check("phi(2440) > 0, which is what the criterion needs",
      float(phi_lo(2440).lower()) > 0,
      "phi(2440) >= %.4f" % float(phi_lo(2440).lower()))

check("phi(2433) > 0, so the criterion closes there",
      float(phi_lo(2433).lower()) > 0,
      "phi(2433) >= %.4f" % float(phi_lo(2433).lower()))

margin = grab(r"gives \$\\varphi\(2433\)>([0-9]+)\$", "the stated margin at k=2433")
m = float(margin.str(20, radius=False))
check("stated margin %s at k=2433" % margin.str(10, radius=False),
      float(phi_lo(2433).lower()) > m,
      "phi(2433) >= %.4f, claim > %.0f" % (float(phi_lo(2433).lower()), m))

# phi(2432) < 0 needs an UPPER bound on phi, i.e. a lower bound on R, so it
# cannot be certified from the one-sided inputs above; the sweep covers
# k <= 2439 regardless, so the threshold claim does not rest on it.
print("%-54s %s" % ("phi(2432) < 0", "not checked"))
print("    needs a LOWER bound on R(2432), which the one-sided certified")
print("    inputs do not provide; eq:full-sweep-ranges covers k <= 2439 anyway")

print()
if fails:
    print("FAILED: %d check(s): %s" % (len(fails), ", ".join(fails)))
    sys.exit(1)
print("all checks pass")

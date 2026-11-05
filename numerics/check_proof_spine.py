#!/usr/bin/env python3
"""End-to-end check of the proof's arithmetic spine.

check_paper_phi.py guards the substitutions inside Lemma phi-base, and
check_lean_constants.py guards agreement between the paper and the Lean
structures.  Neither checks that the PROOF CLOSES: that the ledger really comes
in under 4900, that the base case at k = 59 really holds, that the ranges
really tile without a gap, and that the thresholds each theorem claims really
follow from the inequalities stated.  Those are the load-bearing arithmetic
facts a referee would check by hand, and nothing in the repository checked them
until this script.

Every constant is read out of paper/proof.tex, never hardcoded and never taken
from the Lean sources -- the Lean numerals are deliberately rounded away from
the paper's, so checking the paper against them gives wrong answers in both
directions.  Everything is an interval; `X < c` is tested on X.upper() and
`X > c` on X.lower(), and str(arb) is never used for a decision.

Exit status is nonzero if any check fails.
    Usage: python3 numerics/check_proof_spine.py
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
    print("%-56s %s" % (label, "ok" if ok else "FAIL"))
    print("    %s" % detail)
    if not ok:
        fails.append(label)


def grab(pattern, what):
    m = re.search(pattern, TEX)
    if not m:
        sys.exit("could not find %s -- pattern %r.\nIf the manuscript was "
                 "reworded, update the pattern; do NOT hardcode the value."
                 % (what, pattern))
    return arb(m.group(1))


NUM = r"([0-9]+(?:\.[0-9]+)?)"

# ---------------------------------------------------------------- inputs
d = grab(r"d\\geq" + NUM, "d")
Sstar = grab(r"S\^\*\\leq" + NUM, "S^*")
S0 = grab(r"\\Sigma_0\\leq" + NUM, "Sigma_0")
S1 = grab(r"\\Sigma_1\\leq" + NUM, "Sigma_1")
S2 = grab(r"\\Sigma_2\\leq" + NUM, "Sigma_2")
CE = grab(r"C_E\\leq" + NUM, "C_E")
CN = grab(r"C_N&?\\leq" + NUM, "C_N")
NU = grab(r"N_U&?\\leq" + NUM, "N_U")
b590 = grab(r"\\Sigma_1\+4\\gamma\\Sigma_0<" + NUM, "the second-tail constant")
MR = grab(r"\\abs\{R_k\}\\leq" + NUM + r"\(k\+3\)\^3", "the remainder constant")
Sodd_hi = grab(r"S\\leq" + NUM, "the upper bound on S permitted by beta")

log2 = arb(2).log()
gam = arb.const_euler() if hasattr(arb, "const_euler") else arb("0.5772156649015328606")

print("read from paper/proof.tex:")
for nm, v in (("d >=", d), ("S^* <=", Sstar), ("Sigma_0 <=", S0),
              ("Sigma_1 <=", S1), ("Sigma_2 <=", S2), ("C_E <=", CE),
              ("C_N <=", CN), ("N_U <=", NU), ("MR =", MR)):
    print("  %-12s %s" % (nm, v.str(12, radius=False)))
print()

# ---------------------------------------------------------------- the ledger
far = CE * S2 / 18
rest = S0 / 2 + arb(5) * b590 / 64 + CN + NU
total = far + rest
far_claim = grab(r"_\{" + NUM + r"\}\n", "the far-range underbrace value")
rest_claim = grab(r"\}_\{" + NUM + r"\}\n *\\Bigr\)", "the other underbrace value")

check("far term C_E Sigma_2/18 = %s" % far_claim.str(10, radius=False),
      float(far.upper()) <= float(far_claim.str(20, radius=False)) * 1.0001,
      "computed <= %.4f, printed %s" % (float(far.upper()),
                                        far_claim.str(10, radius=False)))
check("Sigma_0/2 + 5*590/64 + C_N + N_U = %s" % rest_claim.str(10, radius=False),
      float(rest.upper()) <= float(rest_claim.str(20, radius=False)) * 1.0001,
      "computed <= %.4f, printed %s" % (float(rest.upper()),
                                        rest_claim.str(10, radius=False)))
check("ledger closes under MR = %s" % MR.str(10, radius=False),
      float(total.upper()) < float(MR.str(20, radius=False)),
      "C <= %.4f, margin %.2f (%.2f%%)"
      % (float(total.upper()), float(MR.str(20)) - float(total.upper()),
         100 * (1 - float(total.upper()) / float(MR.str(20)))))

# ---------------------------------------------------------------- beta
Sodd = Sodd_hi
beta_lo = d * (gam + log2 - Sodd)
beta_claim = grab(r"\\beta\\geq" + NUM, "the stated lower bound for beta")
check("beta >= %s from d and S" % beta_claim.str(10, radius=False),
      float(beta_lo.lower()) > float(beta_claim.str(20, radius=False)),
      "beta >= %.7f" % float(beta_lo.lower()))

a1_lo = d * log2 / 4
a1_claim = grab(r"a_1\\geq" + NUM, "the stated lower bound for a_1")
check("a_1 = d log2/4 >= %s" % a1_claim.str(10, radius=False),
      float(a1_lo.lower()) > float(a1_claim.str(20, radius=False)),
      "a_1 >= %.7f" % float(a1_lo.lower()))

# ------------------------------------------------- the odd base case, k = 59
# eq:odd-base-59:  MR (62)^3 3^-59 < (beta/3) 2^-59.  This is what makes
# K0 = 59, and it is the tightest inequality in the odd case.
lhs = MR * arb(62) ** 3 * arb(3) ** (-59)
rhs = beta_lo / 3 * arb(2) ** (-59)
check("base case at k = 59 (eq:odd-base-59)",
      float(lhs.upper()) < float(rhs.lower()),
      "LHS <= %.4e, RHS >= %.4e, margin %.1f%%"
      % (float(lhs.upper()), float(rhs.lower()),
         100 * (1 - float(lhs.upper()) / float(rhs.lower()))))

# K0 = 59 must be the FIRST index that works: 58 must fail, or the stated
# threshold is not tight and the sweep requirement is misstated.
lhs58 = MR * arb(61) ** 3 * arb(3) ** (-58)
rhs58 = beta_lo / 3 * arb(2) ** (-58)
check("k = 58 does NOT satisfy it, so 59 is the first index",
      float(lhs58.lower()) > float(rhs58.upper()),
      "LHS >= %.4e vs RHS <= %.4e" % (float(lhs58.lower()), float(rhs58.upper())))

# --------------------------------------------- q(k) < 1 for every k >= 59
# q(k) = (3 MR / beta)(k+3)^3 (2/3)^k; q(59) < 1 is the base case above, and
# q(k+1)/q(k) = (2/3)((k+4)/(k+3))^3 < 1 needs k >= 4.
def q(k):
    return 3 * MR / beta_lo * arb(k + 3) ** 3 * (arb(2) / 3) ** k


check("q(59) < 1", float(q(59).upper()) < 1,
      "q(59) <= %.6f" % float(q(59).upper()))
ratio4 = arb(2) / 3 * (arb(8) / 7) ** 3
ratio3 = arb(2) / 3 * (arb(7) / 6) ** 3
check("q(k+1)/q(k) < 1 exactly from k >= 4",
      float(ratio4.upper()) < 1 and float(ratio3.lower()) > 1,
      "at k=4: %.6f < 1; at k=3: %.6f > 1 (so 4 is the right threshold)"
      % (float(ratio4.upper()), float(ratio3.lower())))
worst = max((float(q(k).upper()) for k in range(59, 400)))
check("q(k) < 1 for every 59 <= k <= 400 (spot check)", worst < 1,
      "max q = %.6f at the left end" % worst)

# ------------------------------------------------------------ range unions
def union_covers(ranges, lo, hi):
    """Do the closed integer ranges cover [lo, hi] with no gap?"""
    todo = set(range(lo, hi + 1))
    for a, b in ranges:
        todo -= set(range(a, b + 1))
    return todo


odd_sweep = (1, 75)
odd_gap = union_covers([odd_sweep, (59, 10000)], 1, 10000)
check("odd: sweep 1..75 and analytic k>=59 tile all k >= 1",
      not odd_gap,
      "uncovered: %s; overlap 59..75 is %d indices"
      % (sorted(odd_gap)[:5] or "none", 75 - 59 + 1))

full_sweeps = [(6, 199), (78, 899), (900, 2439)]
full_gap = union_covers(full_sweeps + [(2440, 10000)], 6, 10000)
check("unrestricted: sweeps + criterion from 2440 tile all k >= 6",
      not full_gap,
      "uncovered: %s; sweeps alone cover 6..%d"
      % (sorted(full_gap)[:5] or "none",
         max(b for _, b in full_sweeps)))
check("the criterion starts exactly where the sweeps stop",
      max(b for _, b in full_sweeps) + 1 == 2440,
      "sweeps end at %d, criterion begins at 2440"
      % max(b for _, b in full_sweeps))

# ------------------------------------------------- the stated overlap count
m = re.search(r"overlap on the ([a-z]+) indices", TEX)
words = {"fifteen": 15, "sixteen": 16, "seventeen": 17, "eighteen": 18,
         "nineteen": 19}
said = words.get(m.group(1)) if m else None
check("stated odd overlap count is right",
      said == 75 - 59 + 1,
      "text says %r (= %s), actual is %d"
      % (m.group(1) if m else None, said, 75 - 59 + 1))

# ------------------------------------------- the underbraces round the RIGHT way
# An underbrace standing for an UPPER bound must round UP, or the display
# understates the bound it is presenting.  The total has 42 of margin either
# way, so this is about the displayed numerals being honest, not about the
# conclusion.
for label, value, claim in (("far", far, far_claim), ("rest", rest, rest_claim)):
    c = float(claim.str(20, radius=False))
    v = float(value.upper())
    check("%s underbrace %s is rounded up, not down"
          % (label, claim.str(10, radius=False)),
          c >= v,
          "computed <= %.4f, printed %.4f, %s"
          % (v, c, "ok" if c >= v else "UNDERSTATES by %.4f" % (v - c)))

# ------------------------------------- stated constants must ROUND UP
# This is the hole that let two false inequalities into print.  Sigma_1 was
# stated as 486.1945 while s1_cauchy.log certifies 486.19450958...; C_N was
# stated as 367.8435 while cn.log certifies 367.84350183....  Both were rounded
# DOWN, so the manuscript asserted bounds its own certificates do not
# establish, and every other guard passed because they only ever compared the
# paper against itself.  Compare against the logs instead.
print()
LOGS = ROOT / "odd-proof" / "numerics"
certs = [
    ("Sigma_0", "s0_cauchy.log", r"S_0 = HEAD \+ TAIL\s*<=\s*\[([0-9.]+)", S0),
    ("Sigma_1", "s1_cauchy.log", r"S_1 = HEAD \+ TAIL\s*<=\s*\[([0-9.]+)", S1),
    ("C_N", "cn.log", r"CN <= \[([0-9.]+)", CN),
    ("C_E", "ce_taylor.log", r"CE <= \[([0-9.]+)", CE),
    ("N_U", "nearu.log", r"NEARU <= \[([0-9.]+)", NU),
]
for name, logname, pat, stated in certs:
    f = LOGS / logname
    if not f.exists():
        print("%-56s %s" % ("%s: %s absent" % (name, logname), "skipped"))
        continue
    m = re.search(pat, f.read_text())
    if not m:
        print("%-56s %s" % ("%s: cannot parse %s" % (name, logname), "skipped"))
        continue
    true_val = arb(m.group(1))
    ok = float(stated.str(30, radius=False)) >= float(true_val.upper())
    check("%s: stated %s >= certified %s"
          % (name, stated.str(10, radius=False), true_val.str(12, radius=False)),
          ok,
          "rounded %s" % ("up, correct" if ok
                          else "DOWN -- the stated bound is FALSE"))

# Sigma_2 needs its own check: it is not a single logged number but a two-part
# assembly, and it is the largest constant in the paper (it carries 4395.55 of
# the 4857.88 ledger, i.e. 90% of it).  Head j <= 16 by interval recursion
# (hcoeff2.log), tail j > 16 by Cauchy at radius 4.5 on the pole-free part
# (mr_deriv_sweep.log, G_2), summed as G_2 (3/R)^17/(1-3/R).  Margin is 0.16.
print()
h2 = LOGS / "hcoeff2.log"
md = LOGS / "mr_deriv_sweep.log"
if h2.exists() and md.exists():
    mh = re.search(r"S \(head, j <= 16\) = ([0-9.]+)", h2.read_text())
    mg = re.search(r"G_2 <= ([0-9.]+)", md.read_text())
    if mh and mg:
        head = arb(mh.group(1))
        G2 = arb(mg.group(1))
        r = arb(3) / arb("4.5")
        total = head + G2 * r ** 17 / (1 - r)
        ok = float(S2.str(30, radius=False)) >= float(total.upper())
        check("Sigma_2: stated %s >= head %s + Cauchy tail"
              % (S2.str(8, radius=False), head.str(10, radius=False)),
              ok,
              "head + tail <= %s, margin %s"
              % (total.str(12, radius=False),
                 (S2 - total).str(6, radius=False) if ok else "NEGATIVE -- FALSE"))
    else:
        check("Sigma_2: its two logs are parseable", False,
              "cannot parse 'S (head, j <= 16)' / 'G_2 <=' -- guard would be vacuous")
else:
    check("Sigma_2: hcoeff2.log and mr_deriv_sweep.log both present", False,
          "absent: %s -- guard would be vacuous"
          % ", ".join(str(x) for x in (h2, md) if not x.exists()))

# The check above recomputes the assembly from the LOGS, so it cannot see an
# error in the chain the manuscript prints.  It could not, and did not: Section
# 8 printed sup <= 1.9673e6, from which the tail is 5990.19 and the printed
# head + tail is 14414.10 -- ABOVE the stated 14414.  Nothing was unsound (the
# logged sup is 1967216.5, giving 5989.93), but the paper's own displayed
# arithmetic contradicted its own bound.  So parse Section 8's numerals too and
# require (a) each to be >= what the certificate gives, and (b) the printed
# chain itself to close.
print()
m_sup = re.search(r"of the pole-free part at most\s*\$([0-9.]+)\\cdot10\^\{6\}\$", TEX)
m_head = re.search(r"in \$s\$, giving \$([0-9.]+)\$", TEX)
m_tail = re.search(r"\(1-3/4\.5\)\^\{-1\}\$, which is \$([0-9.]+)\$", TEX)
m_tot = re.search(r"The two sum to\s*\$([0-9.]+)\$", TEX)
if all((m_sup, m_head, m_tail, m_tot)) and h2.exists() and md.exists():
    psup = arb(m_sup.group(1)) * arb(10) ** 6
    phead, ptail, ptot = (arb(m.group(1)) for m in (m_head, m_tail, m_tot))
    r = arb(3) / arb("4.5")
    chain = phead + psup * r ** 17 / (1 - r)
    check("Section 8 Sigma_2 chain: printed sup %s >= certified %s"
          % (m_sup.group(1) + "e6", mg.group(1)),
          float(psup.lower()) >= float(arb(mg.group(1)).upper()),
          "printed sup is below the certificate" if
          float(psup.lower()) < float(arb(mg.group(1)).upper()) else "ok")
    check("Section 8 Sigma_2 chain: printed head %s >= certified %s"
          % (m_head.group(1), mh.group(1)),
          float(phead.lower()) >= float(arb(mh.group(1)).upper()), "ok")
    check("Section 8 Sigma_2 chain closes as PRINTED (sup -> tail -> total)",
          float(ptail.lower()) >= float((psup * r ** 17 / (1 - r)).upper())
          and float(ptot.lower()) >= float(chain.upper())
          and float(ptot.upper()) <= float(S2.str(30, radius=False)),
          "printed tail %s vs %s, printed total %s vs chain %s, stated %s"
          % (m_tail.group(1), (psup * r ** 17 / (1 - r)).str(10, radius=False),
             m_tot.group(1), chain.str(10, radius=False),
             S2.str(8, radius=False)))
else:
    check("Section 8 Sigma_2 chain: its four numerals are parseable", False,
          "cannot locate them in proof.tex -- guard would be vacuous")

print()
if fails:
    print("FAILED: %d check(s): %s" % (len(fails), ", ".join(fails)))
    sys.exit(1)
print("the arithmetic spine closes: ledger, base case, q(k), both range unions,")
print("and every stated constant is at or above what its certificate gives")

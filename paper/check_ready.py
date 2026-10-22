#!/usr/bin/env python3
"""Pre-submission gate for paper/proof.tex.

The numerics guards (numerics/check_paper_phi.py, numerics/check_lean_constants.py)
check that the constants agree and that the arithmetic holds.  Nothing checked
that the manuscript is actually fit to send, and the failure mode is quiet: the
AI-disclosure placeholder compiled into a clean 21-page PDF with zero LaTeX
errors and zero undefined references, so every signal the repository had said
the paper was fine.

This script is the missing signal.  It exits nonzero while any submission
blocker is present, so "all checks pass" can never coexist with one.

    Usage: python3 paper/check_ready.py
"""
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
TEX = ROOT / "paper" / "proof.tex"
PDF = ROOT / "paper" / "proof.pdf"
PROOFMD = ROOT / "odd-proof" / "PROOF.md"
ODDLEAN = ROOT / "Odd" / "Basic.lean"

tex = TEX.read_text()
fails = []
notes = []


def check(label, ok, detail=""):
    print("%-58s %s" % (label, "ok" if ok else "BLOCKER"))
    if detail:
        print("    %s" % detail)
    if not ok:
        fails.append(label)


# --- 1. nothing unfinished left in the text -------------------------------
# Only the document body matters; a TODO inside a LaTeX comment is a note to
# self, not something a referee sees, so comments are stripped first.
body = re.sub(r"(?m)(?<!\\)%.*$", "", tex)
bad = [w for w in ("PLACEHOLDER", "TODO", "FIXME", "XXX") if w in body]
check("no unfinished markers in the document body",
      not bad,
      "found %s in text that compiles into the PDF" % ", ".join(bad) if bad
      else "checked PLACEHOLDER, TODO, FIXME, XXX")

# --- 2. the AI disclosure is real ----------------------------------------
m = re.search(r"\\section\*\{Statement on the use of AI\}(.*?)"
              r"(?:\\section\*|\\begin\{thebibliography\})", tex, re.S)
if m is None:
    check("AI-disclosure section present", False,
          "no \\section*{Statement on the use of AI} found")
else:
    sec = re.sub(r"(?m)(?<!\\)%.*$", "", m.group(1)).strip()
    words = len(re.findall(r"[A-Za-z]{2,}", sec))
    check("AI-disclosure section has real wording",
          "PLACEHOLDER" not in sec and words >= 25,
          "%d words" % words)
    notes_pending_ai = ("The AI disclosure is a complete statement but was "
                        "drafted here, not taken from the author's wording of "
                        "record (the Euclidean-distance-deflation L-infinity "
                        "paper). Reconcile the two before submission.")

# --- 3. the remainder range agrees in all three places -------------------
# Widening any of these silently re-opens the sign gap; CLAUDE.md explains why.
pm = PROOFMD.read_text() if PROOFMD.exists() else ""
ol = ODDLEAN.read_text() if ODDLEAN.exists() else ""
check("paper states prop:odd-remainder on k >= 59",
      re.search(r"label\{prop:odd-remainder\}\s*\nFor every \$k\\geq59\$", tex)
      is not None)
check("paper's intro expansion carries the same range",
      r"(k\geq59)" in tex or r"\ \ (k\geq59)" in tex)
check("PROOF.md (5.1) states k >= 59",
      "for k >= 59,                 (5.1)" in pm)
check("OddNumericalFacts.remainder requires 59 <= k",
      re.search(r"remainder\s*:\s*∀ k : ℕ, 59 ≤ k →", ol) is not None)

# --- 4. the committed PDF is not stale -----------------------------------
if PDF.exists():
    check("proof.pdf is at least as new as proof.tex",
          PDF.stat().st_mtime >= TEX.stat().st_mtime,
          "regenerate with two passes of pdflatex and commit it alongside")
else:
    check("proof.pdf present", False)

# --- 5. things only the author can clear ---------------------------------
# Reported, not enforced: the script cannot see GitHub from here.
if "github.com/jaideepsaipadhi/erdos-sums-almost-primes" in tex:
    notes.append("Section 8 cites the repository by URL. It must be PUBLIC, or "
                 "archived with a DOI, before submission -- a private link is "
                 "worse than none in a paper whose contribution is in part a "
                 "certification.")
try:
    br = subprocess.run(["git", "-C", str(ROOT), "rev-parse", "--abbrev-ref", "HEAD"],
                        capture_output=True, text=True, timeout=10).stdout.strip()
    if br and br != "main":
        notes.append("On branch %r: the paper changes are not on main yet." % br)
except Exception:
    pass
try:
    notes.append(notes_pending_ai)
except NameError:
    pass
notes.append("Lean is not built in this container, so Section 8 and Table 1 "
             "describe a state no green build has confirmed. Run the `lean` "
             "workflow before submission -- and check steps > 0, since a run "
             "with no runner reports the same conclusion as a build error "
             "(see the comment block in .github/workflows/lean.yml).")

print()
for n in notes:
    print("NOTE: %s" % n)

print()
if fails:
    print("NOT READY: %d blocker(s): %s" % (len(fails), ", ".join(fails)))
    sys.exit(1)
print("no blockers found in the manuscript itself; see the notes above")

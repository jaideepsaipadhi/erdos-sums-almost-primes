#!/usr/bin/env python3
import io, re, sys

PATH = "Banksmartin/Basic.lean"
CANDIDATES = [
    "abel_summation_ratio_log_gen", "abel_summation_ratio_log",
    "integral_term_bound_gen", "integral_term_bound",
    "boundary_term_bound", "sum_ratio_log_bound_gen", "sum_ratio_log_bound",
    "h_p0_bound", "integrableOn_deriv_ratio_log", "hint_ftc",
]

def find_block(s, name):
    m = re.search(r"^theorem " + re.escape(name) + r"(?![A-Za-z0-9_'])", s, re.M)
    if not m:
        return None
    i = m.start()
    head = s[:i]
    ds = head.rfind("/--")
    if ds >= 0 and "-/" in head[ds:] and head[head.find("-/", ds) + 2:].strip() == "":
        i = ds
    nxt = re.search(r"^(theorem|lemma|def|noncomputable def|/--) ", s[m.end():], re.M)
    j = m.end() + nxt.start() if nxt else len(s)
    return i, j

with io.open(PATH, "r", encoding="utf-8") as fh:
    s = fh.read()

removed, changed = [], True
while changed:
    changed = False
    for name in CANDIDATES:
        if name in removed:
            continue
        blk = find_block(s, name)
        if blk is None:
            continue
        i, j = blk
        outside = s[:i] + s[j:]
        if re.search(re.escape(name) + r"(?![A-Za-z0-9_'])", outside):
            continue
        s = outside
        removed.append(name)
        changed = True
print("removed:", removed if removed else "(none)")
kept = [n for n in CANDIDATES if n not in removed]
print("kept (still referenced or absent):", kept if kept else "(none)")
print("remaining sorry count:", s.count("sorry"))
with io.open(PATH, "w", encoding="utf-8") as fh:
    fh.write(s)

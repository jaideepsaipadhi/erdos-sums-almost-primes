# K0 threshold certification — package for many-core execution

Everything here was developed and validated (against independent mpmath
ground truth, brute-force interval-arithmetic checks, and known reference
values) in a single interactive session tonight. See `K0-proof-v6.md` for the
full write-up, including an honest accounting of every bug found along the
way (Sec 8) — read that section before trusting any single number below.

**Bottom line from tonight, single-core:** K0 = 800 (best current estimate,
resting on newly-derived machinery not yet independently reviewed) vs
K0 = 9119 (fully vetted floor, resting only on GLW's own stated bounds plus
pure algebra — see the chat transcript for the derivation of both).

## What your 256 cores actually buy you

1. **Extend and re-verify the certified delta-table** (`delta_parallel.py`).
   Trivially parallel across m — each value is independent. Re-running the
   full table from scratch on your machine, at higher precision than the
   original single-core run, is the single best thing to do first: if it
   reproduces the same values, that's an independent confirmation; if it
   diverges, you've found a real problem.

2. **Refine the s-uniform S1 bound** (`s_uniform_parallel.py`). Also
   trivially parallel across s-subintervals. Push NSUB and P far higher than
   the original session (80 subintervals, P=20000) — try NSUB=2000,
   P=2000000 — and confirm the bound is stable (doesn't move much) as you
   refine further. If it keeps shrinking meaningfully, the original bound
   (alpha=17.538) was itself not fully converged.

3. **Try to fix the noise floor found in the S* extension attempt**
   (`extend_head_highprec.py`). This is the one genuinely open thread from
   tonight: attempting to certify coefficients past i=14 hit a precision
   floor (not a math error — diagnosed in Sec 8) where per-sample Euler-tail
   uncertainty swamps the true (rapidly decaying) signal. The fix is a much
   larger prime cutoff P and precision, which is exactly what your machine
   is for. Run with increasing P (1e7, 1e8, 1e9) and watch whether the
   coefficients keep decaying geometrically past i=14 instead of plateauing.
   If you can push the certified head to i=20-25 without hitting the floor,
   S* may shrink further, which would improve on K0=9119 via the SAME safe
   category of argument (no Lemma-3.3 evaluation needed).

4. **Reassemble everything** (`assemble_final.py`) once you have fresh
   delta-table and s-uniform outputs, to get a from-scratch K0.

5. **The actual computation half of the theorem** (not included here — see
   `K0-proof-v6.md` Sec 10): certified evaluation of f_k itself for
   6 <= k < K0. This is the other half of the Banks-Martin monotonicity
   theorem and is currently done only to k=200. At k^3 scaling, reaching
   k=800 is roughly 64x that cost — very plausibly a good target for a
   256-core machine. The certified.py-style pipeline from the earlier
   session (not included in this package; ask if you want it) would need
   adaptation for k in the 800 range, including a check on whether the
   precision requirement (PREC bits) needs to scale with k, which would
   push the true cost above pure k^3.

## Files

- `K0-proof-v6.md` — full write-up, read this first, especially Sec 0 and Sec 8.
- `core.py` — the underlying G2Engine machinery (Euler product evaluation,
  polar coefficient extraction, etc). Required by `assemble_final.py`.
- `MASTER_CHECK.py` — single-core, single-script reproduction of K0=800 with
  built-in sanity assertions. Run this FIRST as a baseline before scaling up
  anything else, so you have a known-good reference point on your own machine.
- `delta_parallel.py` — parallelized certified delta-table computation.
- `s_uniform_parallel.py` — parallelized s-uniform S1 coefficient bound.
- `extend_head_highprec.py` — attempt to push the S* head further (open thread).
- `assemble_final.py` — combines delta-table + s-uniform output into a final K0.

## Suggested order

```bash
pip install python-flint --break-system-packages

# 1. Reproduce the baseline on your hardware first
python3 MASTER_CHECK.py

# 2. Rebuild the delta table (parallel, trivial to scale up the range too)
python3 delta_parallel.py 9016 250 delta_all_fresh.pkl

# 3. Rebuild the s-uniform S1 bound at higher resolution
python3 s_uniform_parallel.py 2000 2000000 250 supF_highres.pkl

# 4. Reassemble
python3 assemble_final.py delta_all_fresh.pkl supF_highres.pkl

# 5. (open thread) try to push past the i=14 precision floor
python3 extend_head_highprec.py 100000000 20 400 4096
```

Every script prints its own certified enclosures as it goes — nothing here
is a black box. If a number doesn't reproduce, that itself is useful
information (see Sec 8 for how this session treated exactly that situation
each time it came up).

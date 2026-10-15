# GAP-3: Certified low-k verification of f_k < f_{k+1}

Closes the computational half of the monotonicity program: an explicit K0
proves f_k < f_{k+1} only for k >= K0; this verifies it directly for
k = 7 .. K0-1 with certified interval arithmetic. GLW verified k <= 20.

## Method (no asymptotics, no near-singular integral)
f_k = I'_k + (I_k - I'_k) + tail, where:
- I'_k = sum_i c_i * A_{k-i}/2^{k-i}   -- dominant, from certified c_i and the
  certified A_m (delta) table. Cheap.
- (I_k - I'_k) = the S1 correction, evaluated (not bounded) via GLW's
  s = 1+e^{-t} substitution, which removes the s->1 singularity. Certified
  interval quadrature with QUADRATIC convergence (midpoint+derivative panels).
- tail = explicit O(1/(k 2^k)) bound.

Monotonicity test (certified): with g(k)=2^k(1-f_k),
  f_{k+1} > f_k  <=>  g(k) - g(k+1)/2 > 0,  checked on intervals.

## Files
- s1_term.py       : certified S1 evaluator (s1_term_parallel is the fast one)
- lowk_verify.py   : full pipeline + self-check + monotonicity test
- k0_end_to_end.py, core.py : shared certified coefficient/delta machinery

## Validation already done
- general-s coefficient extractor matches independent mpmath at s=1.5 (7 digits)
- S1 term midpoint stable (~1.55 at k=7) across panel counts; lies within GLW's
  own loose bound; QUADRATIC width convergence confirmed (4x per panel doubling)

## Run (on your 256-core machine)
    # 1. self-check FIRST -- must reproduce known k<=20 monotonicity or it HALTS
    python3 lowk_verify.py --selfcheck-only --nproc 230

    # 2. if self-check passes, extend upward
    python3 lowk_verify.py --kmax 740 --nproc 230

Tune NPAN inside lowk_verify (s1_npan) upward until widths at each k are well
below the g(k)-g(k+1)/2 gap. Quadratic convergence means ~30k panels suffices
at low k; scale up with k. If any k stays inconclusive, raise prec_bits(k).

## What this does and does not establish
Establishes (self-contained, no external sign-off): f_k < f_{k+1} on the
computed range, certified. Combined with a valid explicit K0 (the analytic
half, pending Lichtman on the assembly), gives monotonicity for all k > 6.
Does NOT touch the assembly-correctness / exhaustiveness question (GAP-1) --
that remains for the authors.

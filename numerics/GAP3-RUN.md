# GAP-3 run instructions (updated after the speed fix)

## What changed
- S1 integrator now uses prime cutoff P=50,000 (was 2e6): coefficients shift
  <1e-6, far below the enclosure width, but ~50x faster per panel.
- Driver processes k serially and hands the FULL core pool to each k's panel
  loop (the expensive, parallel part). Was ~7 min/k, now seconds/k on 230 cores.

## Run order
1. Self-check (must pass before trusting anything):
       python3 lowk_verify.py --selfcheck-only --nproc 230
   Expect: finishes in a few minutes, prints g(k) for k=7..20.

2. Look at the WIDTHS. To certify f_k<f_{k+1} you need width(g(k)) small
   relative to a1 k^2. At the default NPAN they may still be too wide.
   Increase panels: edit g_interval_clean's default, or the call in the driver,
   setting s1_npan higher. Quadratic convergence: 2x panels -> ~4x tighter.
   Rule of thumb: NPAN ~ 20000-40000 should bring low-k widths well under 1.

3. Once self-check widths are tight AND all k=7..20 show g(k)>0 with
   g(k)-g(k+1)/2 > 0, extend:
       python3 lowk_verify.py --kmax 740 --nproc 230
   (raise prec_bits and NPAN for larger k as needed; the script flags any k
    that stays inconclusive.)

## Trust anchor
The k<=20 self-check reproduces the range GLW verified by hand. If it comes
back all-positive with tight intervals and the monotonicity gaps are
certified, the pipeline is validated; the code looking right is not evidence.
Only then trust k>20 output.

## If widths won't shrink enough
The per-panel enclosure can be tightened further (2nd-derivative term on D_i).
Flag it and I'll add it -- bounded work, not open-ended.

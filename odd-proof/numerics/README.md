# odd-proof/numerics

Certified inputs for `odd-proof/PROOF.md`.  Each script prints an interval or an
explicit upper bound; the committed `.log` beside it is that run.

## Constants of (5.1)

| script | constant | method |
|---|---|---|
| `hcoeff_recursion.py` | `sum_{i<=16} \|g_i\| 3^i <= 8424` | interval recursion, 1600 s-boxes |
| `mr_deriv_sweep.py` | `sup_{\|z\|=4.5} \|G_2\| <= 1.97e6` | 200 theta x 40 s boxes |
| `s0_recursion.py`, `s0_cauchy.py` | `S_0 <= 44.5987` | first-order pole; head by recursion, tail by Cauchy |
| `s1_recursion.py`, `s1_cauchy.py` | `S_1 <= 486.1945` | second-order pole; head by recursion, tail by Cauchy |
| `cn_certified.py` | `CN <= 367.8435` | odd Euler-product recursion (Moebius prime zeta) + Cauchy tail |
| `nearu_certified.py` | `NEARU <= 26.0962` | exact head to k=400 + explicit envelope |
| `ce_taylor.py` | `CE <= 5.48910` (log: `5.4890962927`) | Taylor model in eps, whole range at once |

Together these give `C = CE S/18 + S_0/2 + 5*590/64 + CN + NEARU = 4857.9`,
and (5.1) is stated with `C = 4900`.

The 0.9% of margin there is an artefact of the `NS = 1600` setting, not of the
method: `hcoeff3200.log` halves the box width and gives head `7890.6376` in
place of `8423.9098`, hence `S_2 <= 13881` and `C = 4695.2` — 4.2% of margin.
The head is still falling at `NS = 3200`.  Nothing downstream moves either
way: `K0 = 59` at `C = 4900`, at `C = 4700` and at `C = 4695.2`, and
`MR <= 4900` stays true a fortiori, so the finer run is recorded here as
headroom under the stated budget rather than substituted into it.  It answers
the obvious question about that margin: the 0.9% is the box width, not the
method running out of room.

## Certified values of g_k

`fodd_run.py` at 1000-bit precision; `fodd75.log` reaches k = 75, which is what
section 6 needs (the analytic threshold is K0 = 59).

## Reproducing

    pip install python-flint sympy      # s1_cauchy.py needs sympy as well

Every log below was regenerated from a clean checkout on 2026-10-14 and
matched the committed file exactly, to every printed digit:

    python3 ce_taylor.py                      -> ce_taylor.log
    python3 nearu_certified.py                -> nearu.log
    python3 cn_certified.py                   -> cn.log
    python3 s0_recursion.py 16                -> s0_head.log
    python3 s0_cauchy.py                      -> s0_cauchy.log
    python3 s1_recursion.py                   -> s1_head.log
    python3 s1_cauchy.py                      -> s1_cauchy.log
    python3 hcoeff_recursion.py 16 1600       -> hcoeff2.log
    python3 hcoeff_recursion.py 16 3200       -> hcoeff3200.log
    python3 mr_deriv_sweep.py                 -> mr_deriv_sweep.log

Two of those arguments are not the defaults, and running the script bare does
NOT reproduce its log:

  * `s0_recursion.py` defaults to NMAX = 40; the log of record is NMAX = 16,
    the split point used by s0_cauchy.py for the tail.
  * `hcoeff_recursion.py` defaults to NMAX = 40, NS = 40.

`mr_deriv_sweep.log` and the `fodd*` logs were captured with `nohup ... 2>&1`,
so their progress lines are interleaved with the results; compare the result
lines only.

## Notes

`S_0`, `S_1`, `CN`, `NEARU` and `CE` quantify what earlier drafts of section 5.1
left as "(lower order)".  `CE` in particular is not lower order: it multiplies
the leading term, and moving from the implicit `CE = 3` to the true `5.48910`
is what takes `C` from 2402.3 to 4857 and `K0` from 57 to 59.

`ce_taylor.py` supersedes two earlier attempts (a point sweep and a box sweep)
that could not certify the range: the constants are ratios in which zeta's pole
cancels, and interval evaluation on boxes of `s` loses that cancellation.

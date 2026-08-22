# odd-proof/numerics

Certified inputs for `odd-proof/PROOF.md`.  Each script prints an interval or an
explicit upper bound; the committed `.log` beside it is that run.

## Constants of (5.1)

| script | constant | method |
|---|---|---|
| `hcoeff_recursion.py` | `sum_{i<=16} \|g_i\| 3^i <= 8424` | interval recursion, 1600 s-boxes |
| `mr_deriv_sweep.py` | `sup_{\|z\|=4.5} \|G_2\| <= 1.97e6` | 200 theta x 40 s boxes |
| `s0_recursion.py`, `s0_cauchy.py` | `S_0 <= 44.6` | first-order pole; head by recursion, tail by Cauchy |
| `s1_recursion.py` | `S_1 <= 453.1` | second-order pole, head by recursion |
| `cn_recursion.py` | `CN <= 364` | odd Euler-product recursion + Cauchy tail |
| `nearu_bound.py` | `NEARU <= 24.68` | exact head to k=400 + explicit envelope |
| `ce_taylor.py` | `CE <= 5.4891` | Taylor model in eps, whole range at once |

Together these give `C = CE S/18 + S_0/2 + 9 S_1/128 + CN + NEARU = 4838.4`,
and (5.1) is stated with `C = 4900`.

## Certified values of f_k^odd

`fodd_run.py` at 1000-bit precision; `fodd60.log` reaches k = 60, which is what
section 6 needs (the analytic threshold is K0 = 59).

## Notes

`S_0`, `S_1`, `CN`, `NEARU` and `CE` quantify what earlier drafts of section 5.1
left as "(lower order)".  `CE` in particular is not lower order: it multiplies
the leading term, and moving from the implicit `CE = 3` to the true `5.4891`
is what takes `C` from 2402.3 to 4838 and `K0` from 57 to 59.

`ce_taylor.py` supersedes two earlier attempts (a point sweep and a box sweep)
that could not certify the range: the constants are ratios in which zeta's pole
cancels, and interval evaluation on boxes of `s` loses that cancellation.

Superseded working notes, kept for their error histories (§8 in each).

Their constants and thresholds are NOT current. The authoritative statement
is `NumericalFacts` in Banksmartin/Basic.lean, with the certified values in
bm-rebuild-v21/uv_constants.json and gamma_constant.json (commit 3fce4d3:
alpha_+ 15.425661, Gamma 104.5196, K0 78, K1 2433).

  v5  K0 = 3527   (two accounting errors, see v6 §8)
  v6  K0 = 800    (superseded by v7)
  v7  K0 = 9009 conservative / 741 tight

  sweep_79_734.log  the criterion sweep from k = 79, before the regenerated
                    alpha_+ and Gamma lowered the threshold to 78.  The
                    current run is bm-rebuild-v21/sweep_78_734.log, which
                    reaches further down: k=78 gives crit_lower = 0.91,
                    where this one starts at k=79 with 7.15.

## Correction, 2026-10-22

`K0-proof-v5.md:43` states `d = 0.3786948881` and says it matches GLW's. That
7th digit is wrong: interval arithmetic over the primes to `4e7`, with the tail
bounded by `2/X`, gives

    d = (1/4) prod_{p>=3} (1 + 1/(p(p-2)))  in  [0.378695031521, 0.378695050456]

so the true value is `0.3786950315...`, and `v6`'s `0.3786950 +/- 4e-7` is the
consistent one. The manuscript's certified `d >= 0.3786949` is a valid lower
bound for the true value and is unaffected; `v5`'s figure would have been below
it. Flagged because Section 8 of the paper now cites this repository by URL, so
a reader can reach this file. If `0.3786948881` was ever taken from \cite{GLW},
check which side is off before relying on it.

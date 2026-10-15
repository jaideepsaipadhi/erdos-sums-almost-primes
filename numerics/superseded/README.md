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

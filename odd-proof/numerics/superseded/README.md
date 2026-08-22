Earlier attempts, kept for provenance.  None is an input to `odd-proof/PROOF.md`.

  fodd_certified.py, fodd_head.py, fodd_series.py
      earlier routes to the certified f_k^odd; `fodd_run.py` supersedes them.
  hcoeff_recursion2.py, hcoeff_recursion3.py
      intermediate versions of the interval recursion for S.
  mr_deriv_certified.py
      superseded by `mr_deriv_sweep.py`, which subdivides in s.

  g_k.py, g_k.log, g_k40.log, mr_certified.py
      the earlier route via f_k^odd = f_k - g_{k-1} with g_k = int 2^-s P_k(s),
      and the Cauchy bound on Htilde it needed.  The current proof works with
      f_k^odd directly and does not use g_k.
  hcoeff.log, hcoeff3.log
      earlier NMAX for the interval recursion.  hcoeff2.log is the run that
      gives the cited sum_{i<=16}|g_i|3^i = 8423.909789 over 1600 s-boxes.

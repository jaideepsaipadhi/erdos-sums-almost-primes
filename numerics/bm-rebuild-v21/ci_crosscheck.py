"""Method B (uncertified, independent): c_i via direct Euler-product evaluation
on |z|=1 + Cauchy/FFT extraction. Prime tail p>Pc added via mpmath.primezeta
(different code path & library function from the certified log-series route).
Per-prime tail identity: -log(1-z/p) + z log(1-1/p) = sum_{j>=2} (z^j - z)/(j p^j).
Cross-validates ci_certified.py; run both and require FFT values inside balls."""
# (executable version of the check run in-session; see session log)

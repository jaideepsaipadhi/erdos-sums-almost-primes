# Refined acceptance gate — drop-in for bm-rebuild-v21/

    cd /workspace
    tar xzf refined-gate.tar.gz
    cp refined-gate/* bm-rebuild-v21/
    cd bm-rebuild-v21
    python3 crossval_refined.py /workspace/certificate-k200.json

Tests |implied E1(k) - M2(k)| <= Gamma (=105.41) at every certificate point
k in [100,200]. PASS => refined K0=79 accepted (pending the [810,899] sweep
slice). Any FAIL => K0=735 fallback stands; paste output to Claude.
Expected: all OK with deviation ratios ~0.01.

Both verdict paths smoke-tested: a planted +0.5 offset reads back as
ratio 0.0047 exactly; a planted +200 violation FAILs at ratio 1.8974 exactly.

Files: crossval_refined.py (the gate), bhat_signed_N60.json (signed
[z^i]G2^(1,0)(1,z), P=2e6, i<=60), gamma_constant.json (Gamma + components),
gamma2_certified.json / gamma2_s1_signed.json (second s-derivative sweep,
600 boxes, invariant held, finite-difference validated to ratios 0.999-1.001),
s2_table.py (certified A2/S2 series), gamma2_sweep.py + crit_refined.py
(provenance: the sweep and the refined criterion, K0=79 provisional,
contiguous positive [79,810] verified, [810,899] slice pending).

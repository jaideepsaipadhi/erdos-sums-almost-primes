
## Status (this session)

`Odd/Basic.lean` builds with zero sorries.  `fOdd_decreasing` is proved from
`OddNumericalFacts`, which assumes PROOF.md §§2-5 as certified inputs.

### Toward discharging `OddNumericalFacts.remainder`

The following are proved and are the start of deriving §§2-5 rather than
assuming them.  They are not load-bearing for `fOdd_decreasing`:

- `zeta_laurent_constant` - lim (zeta(s) - 1/(s-1)) = gamma  [Mathlib gap]
- `zetaRegFull_analyticAt_one` - zeta - 1/(s-1) extends analytically  [Mathlib gap]
- `eps_zeta_uniform` - |eps zeta(1+eps) - 1 - gamma eps| <= C eps^2
- `uOf_strictAnti`, `uOf_image`, `sOf` - the u = log zeta substitution
- `uOf_change_of_variables`, `integral_substitute`
- `fOdd_u_form` - g_k as a u-integral with exact powers
- `jacobian_signed`, `eps_of_u_signed`, `jacobian_u_signed`
- `hCoeff_taylor` - signed second-order coefficient expansion
- `gamma_normalised{,_two,_three}` - the three Gamma integrals

### Remaining for Option 2 (deriving `remainder`)

Step D needs `sum_j bHatOdd j * 2^j = 2 dConst (log 2 - Sodd)`, the
s-derivative counterpart of `hCoeff_sum_two`.  Either derived (differentiating
the Euler product in s) or added to the certified inputs.

### Note on the substitution (no PROOF.md error)

PROOF.md §2 correctly uses u = log zeta(s), and (2.2) is exactly
`eps_of_u_signed`.  The Lean development initially used s = 1 + e^-u
(from item 5's `substitution_near_pole`), which does NOT make the u^{k-j}
factors powers of the integration variable; that route was abandoned and
replaced by `uOf_change_of_variables` / `integral_substitute`, matching
PROOF.md.  Formulas (2.3)-(2.5) line up with `gamma_normalised{,_two,_three}`
and `jacobian_u_signed`'s 2 gamma coefficient.

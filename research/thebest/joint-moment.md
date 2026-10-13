# A mixed witness–numerator moment as a structural escape

This is a proposed analytic research direction, not a proved improvement to Cycle25. All numerical gains below are local and conditional. Source: manuscript B0.3–B0.5, especially B0.9, B0.18 and B0.38–B0.47.

Write `A_u` for a centrally normalized, reflected plain numerator profile, of length `U^n`; remove the outside coefficient and slot factors of B0.41 first. On a fixed witness/amplitude cell, `#E <= U^(R+epsilon)`, `|M_r|² >= U^(delta*r-o(1))`, `|S_m|⁴ >= U^(2*delta*m-o(1))`, and `|Q_I|² >= U^(2*q*z-o(1))`. The witness and numerator profiles have independent heights, presentations and possibly conjugate orientations; a new estimate must allow these, as well as the numerator scale supremum in B0.41.

Proposed mixed interfaces, with a common excess exponent `lambda`. Here `B` denotes the fixed buffered zero bin intersected with the natural eligible rows; it contains the witness/amplitude cell `E`. The pointwise reduction below is only claimed on `B`, not on every eligible row:

```
J_I: sum_B |M_r|² |A|² |Q_I|² <= U^(1+lambda+epsilon)
J_P: sum_B |S_m|⁴ |A|² |Q_I|² <= U^(1+lambda+epsilon)
J_L: sum_B |M_r|² |A|²       <= U^(e(r)+lambda+epsilon),
     e(r) = max(1,(1+5*r)/6).
```

These are genuine joint moments. Cauchy–Schwarz after inserting the saturated witness gives, respectively,

```
sum_E |A| <= U^((R + 1 - delta*r - 2*q*z + lambda)/2 + epsilon),
sum_E |A| <= U^((R + 1 - 2*delta*m - 2*q*z + lambda)/2 + epsilon),
sum_E |A| <= U^((R + e(r) - delta*r + lambda)/2 + epsilon).
```

If one uses the same branch selection that proves B0.40, its chosen count line is at most `R`. A uniform joint bound on all three branches would therefore give `R+lambda/2`, replacing the separate count/Hölder exponent `1/4+3R/4-q*z_A/2`. It still uses the row count, but removes its three-quarter Hölder coefficient by inserting the actual witness before taking the numerator moment. No independence of the witness and numerator is assumed in this deduction.

At the binding point of B0.45–B0.48, the reproducible diagnostic gives:

| Quantity | Value |
|---|---:|
| inverse witness length exponent `r` | 0.745699942724 |
| plain witness length exponent `m` | 0.418253633785 |
| reflected numerator exponent `n=1-y/h` | 0.420985160876 |
| row count `R` | 0.590332353526 |
| current numerator exponent | 0.688627440499 |
| largest mixed loss giving a strict local improvement | 0.196590173946 |
| mixed loss available from the pointwise numerator bound, `delta*n` | 0.197587220845 |
| required saving over that pointwise loss | 0.000997046899 |

Set `lambda=delta*n-rho`, where `rho` is the hypothetical saving over the pointwise reduction. Thus the appealing target is not necessarily `lambda=0`: a mixed-moment power saving `rho` slightly larger than `0.00099705` would already cross the current local obstruction. The plot uses this saving as its horizontal axis. This small number is a diagnostic of the binding cell, not a globally sufficient theorem or a certified new boundary.

Why this is missing input: B0.15 gives `|A|² <= U^(delta*n+epsilon)` on these buffered bins, so MI, MP, and B0.9 already prove the interfaces with `lambda=delta*n`. They do not provide the required strict saving. Hölder applied only to existing separate moments permits complete concentration of numerator mass on witness-large rows, so it supplies no decorrelation gain. Multiplying `M` by `A` changes the arithmetic coefficients to a convolution, which is outside MI's Möbius coefficient interface. Multiplying `S_m` by `A` does not produce the single plain fourth moment allowed by MP. Separate witness/numerator heights also preclude replacing their product by a single same-height plain polynomial.

There is a simple scalar sharpness check for the particular interfaces used at this cell. Put `U^R` rows in a set and give each numerator magnitude `U^b`, with `b=(1-R-2*q*z_A)/4`. Give the short inverse and plain witnesses their saturated magnitudes and the marks their saturated amplitudes. Then the selected MI, witness MP, and numerator MP bounds all have exponent exactly one, while the numerator sum has exponent `R+b`, exactly B0.41. Moreover `2*b=0.196590173946 < delta*n`, so the numerator pointwise bound is respected. This is an abstract concentration example for these scalar bounds, not a construction of arithmetic rows; it explains why rearranging the same Hölder inputs cannot force a strict improvement.

A naive product-length heuristic is not favorable: at full witness mark capacity, the inverse effective length `r+n+2*z_I` and the plain effective length `2*m+n+6*kappa*z_P` both equal `1+n=1.420985160876`. These are diagnostics only, not claimed applicability conditions for an unproved mixed theorem. Any useful proof needs arithmetic structure, a restricted exceptional-set estimate, or cancellation beyond merely treating the product as arbitrary coefficients.

The long inverse branch is essential: at its endpoint `r=t=1.163953576509`, `e(t)-delta*t=R`. A result only for the displayed short crossing would leave this equally binding branch untouched. A global improvement also requires a uniform neighborhood in `(delta,p,d)`, the row-dependent reflected-scale supremum, natural row zeros and eligibility, fixed twists and independent heights, coefficient damping from B0.44, and a new full endpoint certificate. The interfaces must be stable under the coefficient shifts; a bound solely at the unshifted value of `n` is insufficient.

A second direction is a sixth numerator moment: if one could prove `sum |A|^6 |Q|² <= U^(1+epsilon)` with capacity `z_6`, Hölder gives `1/6+5R/6-q*z_6/3`. Even with `z_6=0`, its local exponent is `0.658610294605`, below the current value. However `3*n=1.262955482628>1`, so the usual product-length range does not reach this cell. MP does not imply this sixth moment. It is an alternative substantial analytic input, not a consequence of increasing a numerical moment parameter.

Reproduce with `python research/thebest/joint-moment.py` in an environment containing matplotlib. The script writes the numerical JSON and a plot explicitly labeled conditional/local. Constants come from the manuscript's decimal geometry; this experiment is not an interval proof.
